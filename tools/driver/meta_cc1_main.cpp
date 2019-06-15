//===-- meta_cc1_main.cpp - Clang CC1 Compiler Frontend ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is the entry point to the clang -cc1 functionality, which implements the
// core compiler functionality along with a number of additional tools for
// demonstration and testing purposes.
//
//===----------------------------------------------------------------------===//

#include "llvm/Option/Arg.h"
#include "clang/CodeGen/ObjectFilePCHContainerOperations.h"
#include "clang/Driver/DriverDiagnostic.h"
#include "clang/Driver/Options.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticBuffer.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Frontend/Utils.h"
#include "clang/FrontendTool/Utils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Option/ArgList.h"
#include "llvm/Option/OptTable.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"


using namespace clang;
using namespace llvm;

#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Lexer.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/ParseAST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Sema/SemaConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/ParentMap.h"

#include "clang/CodeGen/CodeGenAction.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/MCJIT.h"

#include <iterator>
#include <sstream>
#include <string>
#include<cstdarg>

ArrayRef<const char *> GlobalArgv;
LangOptions LangOps;

template<typename T>
std::string to_string(T *O, unsigned indentation = 0, const PrintingPolicy& Policy = PrintingPolicy(LangOps)) {
	std::string str;
	raw_string_ostream os(str);
	if (O) O->printPretty(os, nullptr, Policy, indentation);
	return os.str();
}

template<typename Derived>
class ASTVisitor : public RecursiveASTVisitor<Derived> {
public:
	typedef RecursiveASTVisitor<Derived> Base;

	bool VisitNamedDecl(NamedDecl *D) {
		if (UsingDirectiveDecl *UDD = dyn_cast_or_null<UsingDirectiveDecl>(D))
			D = UDD->getNominatedNamespace();
		return TryTraverseMetaGeneratedIdentifier(D->getIdentifier());
	}

	bool VisitCXXPseudoDestructorExpr(CXXPseudoDestructorExpr *E) {
		return TryTraverseMetaGeneratedIdentifier(E->getDestroyedTypeIdentifier());
	}

	bool TraverseDependentNameTypeLoc(DependentNameTypeLoc TL) {
		return	Base::TraverseDependentNameTypeLoc(TL) &&
				TryTraverseMetaGeneratedIdentifier(TL.getTypePtr()->getIdentifier());
	}

	bool TraverseDependentTemplateSpecializationTypeLoc(DependentTemplateSpecializationTypeLoc TL) {
		return	Base::TraverseDependentTemplateSpecializationTypeLoc(TL) &&
				TryTraverseMetaGeneratedIdentifier(TL.getTypePtr()->getIdentifier());
	}

	bool TraverseNestedNameSpecifierLoc(NestedNameSpecifierLoc NNS) {
		bool result = Base::TraverseNestedNameSpecifierLoc(NNS);
		if (NNS)
			result = result && TryTraverseMetaGeneratedIdentifier(NNS.getNestedNameSpecifier()->getAsIdentifier());
		return result;
	}

	bool TraverseDeclarationNameInfo(DeclarationNameInfo NameInfo) {
		const std::string str = NameInfo.getAsString();
		return	Base::TraverseDeclarationNameInfo(NameInfo) &&
				TryTraverseMetaGeneratedIdentifier(NameInfo.getName().getAsIdentifierInfo());
	}

	bool TraverseLambdaCapture(LambdaExpr *LE, const LambdaCapture *C) {
		return VisitNamedDecl(C->getCapturedVar()) && Base::TraverseLambdaCapture(LE, C);
	}

	bool TraverseMetaGeneratedIdentifier(const IdentifierInfo *II) {
		assert(II->isMetaGenerated());
		return Base::getDerived().TraverseStmt(II->getFETokenInfo<Expr>());
	}
protected:
	bool TryTraverseMetaGeneratedIdentifier(const IdentifierInfo *II) {
		bool result = true;
		if (II && II->isMetaGenerated() && processed.find(II) == processed.end()) {
			processed.insert(II);
			result = Base::getDerived().TraverseMetaGeneratedIdentifier(II);
		}
		return result;
	}
private:
	std::set<const IdentifierInfo*> processed;
};

template<typename Derived>
class StageNestingVisitor : public ASTVisitor<Derived> {
public:
	typedef ASTVisitor<Derived> Base;
	StageNestingVisitor() : stageNesting(0), qqNesting(0) {}
	virtual ~StageNestingVisitor() {}

#define DEF_TRAVERSE_META(DECL, TYPE)		\
	bool Traverse##DECL(TYPE *d) {			\
		StageNestingRAIIObject RAII(*this);	\
		return Base::Traverse##DECL(d);		\
	}

	DEF_TRAVERSE_META(UnaryInline, UnaryOperator)
	DEF_TRAVERSE_META(ExecuteStmt, ExecuteStmt)
	DEF_TRAVERSE_META(InlineDecl, InlineDecl)
	DEF_TRAVERSE_META(ExecuteDecl, ExecuteDecl)
	DEF_TRAVERSE_META(DefDecl, DefDecl)
#undef DEF_TRAVERSE_META
	
	bool TraverseDecl(Decl *D) {
		return !D || D->isInvalidDecl() ? true : Base::TraverseDecl(D);
	}

	bool TraverseQuasiQuoteExpr(QuasiQuoteExpr *E) {
		++qqNesting;
		bool result = Base::TraverseQuasiQuoteExpr(E);
		--qqNesting;
		return result;
	}

	bool TraverseEscapeDecl(EscapeDecl *D) {
		EscapeRAIIObject RAII(*this);
		return Base::TraverseEscapeDecl(D);
	}
	bool TraverseUnaryEscape(UnaryOperator *O) {
		EscapeRAIIObject RAII(*this);
		return Base::TraverseUnaryEscape(O);
	}

protected:
	struct StageNestingRAIIObject {
		StageNestingVisitor& visitor;
		StageNestingRAIIObject(StageNestingVisitor& visitor) : visitor(visitor)
			{ if (!visitor.qqNesting) ++visitor.stageNesting; }
		~StageNestingRAIIObject() { if (!visitor.qqNesting) --visitor.stageNesting; }
	};
	struct EscapeRAIIObject {
		StageNestingVisitor& visitor;
		EscapeRAIIObject(StageNestingVisitor& visitor) : visitor(visitor) {
			assert(visitor.qqNesting && "escapes are valid only within quasi-quotes");
			visitor.savedQQNestings.push(visitor.qqNesting);
			visitor.qqNesting = 0;
		}
		~EscapeRAIIObject() {
			visitor.qqNesting = visitor.savedQQNestings.top();
			visitor.savedQQNestings.pop();
		}
	};

	unsigned stageNesting;
	unsigned qqNesting;
	std::stack<unsigned> savedQQNestings;
};

class CodeRewriter {
public:
	CodeRewriter(CompilerInstance *C) :
		Rewrite(), SM(C->getSourceManager()), LangOpts(C->getLangOpts()), lastGeneratedII(nullptr) {
		Rewrite.setSourceMgr(SM, LangOpts);
	}
	virtual ~CodeRewriter(){}

	void RewriteCode(SourceRange SR, QuotedElements *Elems, bool rewritingExpr, Stmt *Parent) {
		std::ostringstream os;
		os << to_string(Elems);

		if (!Elems) {	//adjust range to handle removing the element from a comma separated list (e.g. arglist, exprlist)
			SourceLocation TrailingCommaLoc = Lexer::findLocationAfterToken(SR.getEnd(), tok::comma, SM, LangOpts, false);
			if (TrailingCommaLoc.isValid())
				SR.setEnd(TrailingCommaLoc);
			else {	//check for leading comma
				SourceLocation Loc = SR.getBegin();
				if (!Loc.isMacroID() || Lexer::isAtEndOfMacroExpansion(Loc, SM, LangOpts, &Loc)) {
					Token Tok;
					Tok.startToken();
					for (	SourceLocation L = Loc.getLocWithOffset(-1);
							L.getRawEncoding() > 0 && (Lexer::getRawToken(L, Tok, SM, LangOpts) || Tok.is(tok::periodtilde));
							L = SourceLocation::getFromRawEncoding(L.getRawEncoding() - 1)
					);
					if (Tok.is(tok::comma))
						SR.setBegin(Tok.getLocation());
				}
			}
		}
		else if (!rewritingExpr && Elems->isExpr())
			os << ";";
		else if (rewritingExpr)
			if (!Elems->isExpr() && (!Parent || !Expr::classof(Parent))) {
				SourceLocation TrailingSemiLoc = Lexer::findLocationAfterToken(SR.getEnd(), tok::semi, SM, LangOpts, false);
				if (TrailingSemiLoc.isValid())
					SR.setEnd(TrailingSemiLoc);
			}	
		Rewrite.ReplaceText(SR, os.str());
	}

	//@@TODO: Figure out when we should remove the annotation keywords.
	void PruneTypenameKeywordIfNecessary(DependentNameTypeLoc TL, QuotedElements *Elems) {
		if (TL.getElaboratedKeywordLoc().isValid() && !TL.getTypePtr()->getQualifier()) {
			const clang::Type* T = Elems && Elems->isTypeInfo() ? Elems->getTypeInfo()->getTypeLoc().getTypePtr() : nullptr;
			const DependentNameType* DNT;
			if (!Elems || Elems->isParamDeclaration() || T && (T->isBuiltinType() ||
				(DNT = dyn_cast_or_null<DependentNameType>(T)) && DNT->getKeyword() == TL.getTypePtr()->getKeyword())) {
				SourceLocation StartLoc = TL.getElaboratedKeywordLoc();
				unsigned length = SM.getFileOffset(TL.getNameLoc()) - SM.getFileOffset(StartLoc);
				Rewrite.ReplaceText(StartLoc, length, "");
			}
		}
	}

	const RewriteBuffer *getRewriteBufferFor(FileID FID) { return Rewrite.getRewriteBufferFor(FID); }
protected:
	Rewriter		Rewrite;
	SourceManager&	SM;
	LangOptions&	LangOpts;
	const IdentifierInfo* lastGeneratedII;
};

class StageResultRewriter : public ASTConsumer, public CodeRewriter, public StageNestingVisitor<StageResultRewriter> {
public:
	typedef StageNestingVisitor<StageResultRewriter> Base;
	typedef std::vector<QuotedElements*> Inlines;

	StageResultRewriter(CompilerInstance *C, unsigned targetNesting) :
		CodeRewriter(C), maxStageNesting(targetNesting), PM(nullptr) {}

	void HandleTranslationUnit(ASTContext &Context) override {
		iter = inlines.begin();
		TraverseDecl(Context.getTranslationUnitDecl());
		assert(iter == inlines.end());
		inlines.clear();
    }

	bool TraverseStmt(Stmt *S) {
		bool topLevel = PM == nullptr;
		if (topLevel)
			PM = new ParentMap(S);
		bool result = Base::TraverseStmt(S);
		if (topLevel) {
			delete PM;
			PM = nullptr;
		}
		return result;
	}

	bool TraverseMetaGeneratedIdentifier(const IdentifierInfo* II) {
		bool result = Base::TraverseMetaGeneratedIdentifier(II);
		if (!qqNesting && stageNesting + 1 == maxStageNesting &&	//+1 for the current .!
			II->getName().startswith(tok::getPunctuatorSpelling(tok::periodexclaim)))
			lastGeneratedII = II;
		return result;
	}

	bool TraverseDependentNameTypeLoc(DependentNameTypeLoc TL) {
		bool result = Base::TraverseDependentNameTypeLoc(TL);
		if (lastGeneratedII && lastGeneratedII == TL.getTypePtr()->getIdentifier())
			PruneTypenameKeywordIfNecessary(TL, *(iter - 1));
		return result;
	}

	//@@TODO: adopt this logic in a separate final StageResult phase
	//bool TraverseDependentTemplateSpecializationTypeLoc(DependentTemplateSpecializationTypeLoc TL) {
	//	bool result = Base::TraverseDependentTemplateSpecializationTypeLoc(TL);
	//	if (inlinedIdentifiers.find(TL.getTypePtr()->getIdentifier()) != inlinedIdentifiers.end()) {
	//		const DependentTemplateSpecializationType *Type = TL.getTypePtr();
	//		NestedNameSpecifier* NNS = Type->getQualifier();
	//		if (NNS && NNS->getKind() == NestedNameSpecifier::Global) {
	//			SourceLocation StartLoc = TL.getQualifierLoc().getBeginLoc();
	//			if (Type->getKeyword() == ETK_Typename)
	//				StartLoc = TL.getElaboratedKeywordLoc();
	//			unsigned length = SM.getFileOffset(TL.getTemplateNameLoc()) - SM.getFileOffset(StartLoc);
	//			//FIXME:Rewrite.ReplaceText(StartLoc, length, "");
	//		}
	//	}
	//	return result;
	//}

	bool VisitUnaryInline(UnaryOperator *O) {
		Stmt *Parent = PM ? PM->getParent(O) : nullptr;
		return HandleInline(O->getSourceRange(), true, Parent);
	}
	bool VisitInlineDecl(InlineDecl *D) { return HandleInline(D->getSourceRange(), false); }

    bool VisitExecuteStmt(ExecuteStmt *S) { return PruneCode(S->getSourceRange()); }
	bool VisitExecuteDecl(ExecuteDecl *D) { return PruneCode(D->getSourceRange()); }
	bool VisitDefDecl(DefDecl *D) { return PruneCode(D->getSourceRange()); }

	static void AddInline(QuotedElements *ast) { inlines.push_back(ast); }
private:
	bool HandleInline(SourceRange range, bool rewritingExpr, Stmt* Parent = nullptr) {
		if (!qqNesting && stageNesting == maxStageNesting)
			RewriteCode(range, *iter++, rewritingExpr, Parent);
		return true;
	}

	bool PruneCode(SourceRange range) {
		if (!qqNesting && stageNesting == maxStageNesting) {
			//when pruning nested stage code, use a semi to keep it well-formed
			Rewrite.ReplaceText(range, stageNesting == 1 ? "" : ";");
		}
		return true;
	}

	unsigned						maxStageNesting;
	Inlines::const_iterator			iter;
	std::set<const IdentifierInfo*> inlinedIdentifiers;
	ParentMap*						PM;
	static Inlines					inlines;
};

StageResultRewriter::Inlines StageResultRewriter::inlines;

#ifdef _MSC_VER
#   define META_API __declspec(dllexport)
#elif defined(__GNUC__)
#   define META_API __attribute__((visibility("default")))
#else
#   define META_API
#   pragma warning Unknown dynamic link semantics.
#endif

META_API void __meta_inline(void* ast) {
	StageResultRewriter::AddInline((QuotedElements*) ast);
}


class EscapeRewriter : public CodeRewriter, public ASTVisitor<EscapeRewriter> {
public:
	typedef ASTVisitor<EscapeRewriter> Base;
	typedef std::vector<QuotedElements*> Escapes;
	EscapeRewriter(CompilerInstance *C, const Escapes& escapes) :
		C(C), CodeRewriter(C), escapes(escapes) {}

	void HandleQuotedElements(QuotedElements *Elems) {
		HandlerRAIIObject RAII(*this);
		switch(Elems->getType()) {
			case QuotedElements::AST_Expression:
				TraverseStmt(Elems->getExpr());
				break;
			case QuotedElements::AST_StatementOrDeclarationList: {
				Stmt **S = Elems->getStmts();
				for (unsigned i = 0; S[i]; ++i)
					TraverseStmt(S[i]);
				break;
			}
			case QuotedElements::AST_ParameterDeclaration:
				for(auto& P : *Elems->getParams())
					TraverseDecl(P.Param);
				break;
			case QuotedElements::AST_DeclContext: {
				DeclContext *DC = Elems->getDeclContext();
				for (auto D = DC->decls_begin(), DEnd = DC->decls_end(); D != DEnd; ++D)
					TraverseDecl(*D);
				break;
			}
			case QuotedElements::AST_TypeInfo:
				TraverseTypeLoc(Elems->getTypeInfo()->getTypeLoc());
				break;
			default: assert(false);
		}
	}

	bool TraverseStmt(Stmt *S) {
		bool topLevel = PMs.empty();
		if (topLevel)
			PMs.push(new ParentMap(S));
		bool result = Base::TraverseStmt(S);
		if (topLevel) {
			delete PMs.top();
			PMs.pop();
		}
		return result;
	}

	bool TraverseMetaGeneratedIdentifier(const IdentifierInfo *II) {
		ParentMap Parents(II->getFETokenInfo<Expr>());
		PMs.push(&Parents);
		bool result = Base::TraverseMetaGeneratedIdentifier(II);
		
		//@@TODO: maybe check stage nesting/qqNesting here?
		if (II->getName().startswith(tok::getPunctuatorSpelling(tok::periodtilde)))
			lastGeneratedII = II;

		PMs.pop();
		return result;
	}

	bool TraverseDependentNameTypeLoc(DependentNameTypeLoc TL) {
		bool result = Base::TraverseDependentNameTypeLoc(TL);
		if (lastGeneratedII && lastGeneratedII == TL.getTypePtr()->getIdentifier())
			PruneTypenameKeywordIfNecessary(TL, *(iter - 1));
		return result;
	}

	bool VisitEscapeDecl(EscapeDecl *D) { return HandleEscape(D->getSourceRange(), false); }
	bool VisitUnaryEscape(UnaryOperator *O) {
		Stmt *parent;
		SourceRange SR;
		if (!PMs.empty() && (parent = PMs.top()->getParent(O)) && isa<PackExpansionExpr>(parent))
			SR = cast<PackExpansionExpr>(parent)->getSourceRange();
		else
			SR = O->getSourceRange();
		return HandleEscape(SR, true, parent);
	}

private:
	bool HandleEscape(SourceRange SR, bool rewritingExpr, Stmt *Parent = nullptr) {
		RewriteCode(SR, *iter++, rewritingExpr, Parent);
		return true;
	}

	struct HandlerRAIIObject {
		EscapeRewriter& self;
		HandlerRAIIObject(EscapeRewriter& self) : self(self) { self.iter = self.escapes.begin(); }
		~HandlerRAIIObject() { assert(self.iter == self.escapes.end()); self.escapes.clear(); }
	};

	CompilerInstance*		C;
	Escapes					escapes;
	Escapes::const_iterator iter;
	std::stack<ParentMap*>	PMs;
};

QuotedElements* ParseQuotedElements(CompilerInstance *C) {
	Preprocessor& PP = C->getPreprocessor();
	struct EmptyASTConsumer : ASTConsumer {};
	C->setASTConsumer(std::unique_ptr<ASTConsumer>(new EmptyASTConsumer));
	C->createSema(TU_Prefix, nullptr);
	Sema& S = C->getSema();
	std::unique_ptr<Parser> ParseOP(new Parser(PP, S, false));
	Parser &P = *ParseOP.get();
	PP.EnterMainSourceFile();

	DiagnosticConsumer& DC = C->getDiagnosticClient();
	DC.BeginSourceFile(C->getLangOpts(), &PP);
	P.Initialize();
	S.CurContext->setAllowUnresolvedIds();

	unsigned ScopeFlags = Scope::BreakScope	| Scope::ContinueScope	|
						Scope::ControlScope | Scope::DeclScope		|
						Scope::FnScope		| Scope::BlockScope		|
						Scope::ClassScope	| Scope::QuasiQuotesScope;
	Parser::ParseScope QuasiQuotesScope(&P, ScopeFlags);

	QuotedElements* Elems = S.ActOnStartQuasiQuoteExpr(SourceLocation());
	bool result = P.ParseQuotedElements(Elems, tok::eof);
	S.ActOnEndQuasiQuoteExpr(SourceLocation(), SourceLocation(), Elems);
	assert(result);
	DC.EndSourceFile();
	return Elems;
}

bool ResetCompiler(CompilerInstance *C, ArrayRef<const char *> Argv);
FileID SetInputCode(CompilerInstance *C, const std::string& sourceName, const char* sourceText);

EscapeRewriter::Escapes extract_escapes(unsigned total, va_list args) {
	EscapeRewriter::Escapes escapes;
	for (unsigned i = 0; i < total; ++i) {
		QuotedElements* escape = va_arg(args, QuotedElements*);
		escapes.push_back(escape);
	}
	return escapes;
}

void* meta_qq_impl(const char* qq, const EscapeRewriter::Escapes& escapes) {
	assert(qq);
	CompilerInstance *C = new CompilerInstance();	//todo mem leak
	ResetCompiler(C, GlobalArgv);
	const std::string str = std::string(qq);
	FileID file = SetInputCode(C, "__meta_qq.cpp", str.c_str());
	QuotedElements* ast = ParseQuotedElements(C);
	if (!escapes.empty()) {
		EscapeRewriter rewriter(C, escapes);
		rewriter.HandleQuotedElements(ast);

		const RewriteBuffer *RewriteBuf = rewriter.getRewriteBufferFor(file);
		assert(RewriteBuf);
		const std::string finalCode = std::string(RewriteBuf->begin(), RewriteBuf->end());
		if (finalCode.empty())
			ast = nullptr;
		else {
			C->resetAndLeakSema();
			ResetCompiler(C, GlobalArgv);
			SetInputCode(C, "__meta_qq.cpp", finalCode.c_str());
			ast = ParseQuotedElements(C);
		}
	}
	return ast;
}

META_API void* __meta_qq(const char* qq, unsigned totalEscapes, ...) {
	va_list args;
	va_start(args, totalEscapes);
	EscapeRewriter::Escapes escapes = extract_escapes(totalEscapes, args);
	va_end(args);
	return meta_qq_impl(qq, escapes);
}

META_API void* __meta_escape_pack(unsigned total, ...) {
	if (!total)
		return nullptr;
	va_list args;
	va_start(args, total);
	EscapeRewriter::Escapes escapes = extract_escapes(total, args);
	va_end(args);

	std::ostringstream os;
	for (unsigned i = 0; i < total; ++i) {
		if (i) os << ", ";
		os << ".~i" << i;	
	}
	return meta_qq_impl(os.str().c_str(), escapes);
}

class DeclContextMarker : public ASTConsumer, public StageNestingVisitor<DeclContextMarker> {
public:
	typedef StageNestingVisitor<DeclContextMarker> Base;

	void HandleTranslationUnit(ASTContext &Context) override
		{ TraverseDecl(Context.getTranslationUnitDecl()); }

	bool TraverseDecl(Decl *D) {
		DeclContext *DC = dyn_cast_or_null<DeclContext>(D);
		if (DC)
			contextStack.push(DC);
		bool result = Base::TraverseDecl(D);
		if (DC)
			contextStack.pop();
		return result;
	}

	bool VisitCallExpr(CallExpr *C) {
		if (!qqNesting)
			if (FunctionDecl *F = C->getDirectCallee())
				if (IdentifierInfo *II = F->getIdentifier())
					if (II->getName() == "__meta_context" && !contextStack.empty()) {
						DeclContext *DC = contextStack.top();
						while(isa<ExecuteDecl>(DC) || isa<DefDecl>(DC))
							DC = DC->getParent();
						contexts.push_back(DC);
					}
		return true;
	}

	static DeclContext *getNextDeclContext(void) {
		DeclContext *DC = nullptr;
		 if (!contexts.empty()) {
			DC = contexts.front();
			contexts.pop_front();
		}
		return DC;
	}
private:
	std::stack<DeclContext*> contextStack;
	static std::deque<DeclContext*> contexts;
};
std::deque<DeclContext*> DeclContextMarker::contexts;

META_API void* __meta_context() { return DeclContextMarker::getNextDeclContext(); }

class QuasiQuoteRewriter : public SemaConsumer, public ASTVisitor<QuasiQuoteRewriter> {
public:
	typedef ASTVisitor<QuasiQuoteRewriter> Base;
	QuasiQuoteRewriter(CompilerInstance *C) : Rewrite(), Actions(nullptr) {
		Rewrite.setSourceMgr(C->getSourceManager(), C->getLangOpts());
		qqNesting.push(0);
	}

    virtual void InitializeSema(Sema &S) { Actions = &S;}
	virtual void ForgetSema() { Actions = nullptr; }

	void HandleTranslationUnit(ASTContext &Context) override
		{ TraverseDecl(Context.getTranslationUnitDecl()); }

	bool TraverseEscapeDecl(EscapeDecl *D) {
		EscapeRAIIObject RAII(*this);
		return Base::TraverseEscapeDecl(D);
	}
	bool TraverseUnaryEscape(UnaryOperator *O) {
		EscapeRAIIObject RAII(*this);
		return Base::TraverseUnaryEscape(O);
	}

	bool TraverseQuasiQuoteExpr(QuasiQuoteExpr *E) {
		if (!qqNesting.top()++) {
			escapes.push(std::ostringstream());
			totalEscapes.push(0);
		}
		ParentMap Parents(E);
		PMs.push(&Parents);
		bool result = Base::TraverseQuasiQuoteExpr(E);
		if (!--qqNesting.top()) {
			std::ostringstream os;
			std::string qq = to_string(E->getElements());
			if (!qq.empty() && qq.front() != '\"' && qq.back() != '\"')
				qq = std::string("\"") + escapeQuotes(qq) + std::string("\"");
			os << "__meta_qq(" << qq << ", " << totalEscapes.top() << escapes.top().str() << ")";
			Rewrite.ReplaceText(E->getSourceRange(), os.str());
			escapes.pop();
			totalEscapes.pop();
		}
		PMs.pop();
		return result;
	}

	bool TraverseMetaGeneratedIdentifier(const IdentifierInfo *II) {
		ParentMap Parents(II->getFETokenInfo<Expr>());
		PMs.push(&Parents);
		bool result = Base::TraverseMetaGeneratedIdentifier(II);
		PMs.pop();
		return result;
	}

	bool VisitEscapeDecl(EscapeDecl *D) { return HandleEscape(D->getExpr()); }
	bool VisitUnaryEscape(UnaryOperator *O) {
		IdentifierInfo *PackName = nullptr;
		Stmt *parent;
		if (Actions && !PMs.empty() && (parent = PMs.top()->getParent(O)) && isa<PackExpansionExpr>(parent)) {
			Expr *Pattern = cast<PackExpansionExpr>(parent)->getPattern();
			//const std::string str = to_string(Pattern);
			SmallVector<UnexpandedParameterPack, 2> Unexpanded;
			Actions->collectUnexpandedParameterPacks(Pattern, Unexpanded);
			if (Unexpanded.size() == 1) {
				UnexpandedParameterPack &UPP = Unexpanded.front();
				if (const TemplateTypeParmType *TTP = UPP.first.dyn_cast<const TemplateTypeParmType *>())
					PackName = TTP->getIdentifier();
				else
					PackName = UPP.first.get<NamedDecl *>()->getIdentifier();
			}
		}
		return HandleEscape(O->getSubExpr(), PackName);
	}

	const RewriteBuffer *getRewriteBufferFor(FileID FID) { return Rewrite.getRewriteBufferFor(FID); }

private:
	std::string escapeQuotes(const std::string& s) {
		std::string result;
		for(auto i = s.begin(); i != s.end(); ++i) {
			switch(*i) {
				case '\"':	result.append("\\\"");	break;
				case '\'':	result.append("\\\'");	break;
				case '\\':	result.append("\\\\");	break;
				case '\n':	result.append("\\n");	break;
				case '\t':	result.append("\\t");	break;
				default:	result.append(1, *i);	break;
			}
		}
		return result;
	}

	bool HandleEscape(Expr *E, IdentifierInfo *PackName = nullptr) {
		++totalEscapes.top();
		std::string code = to_string(E);
		if (PackName)
			escapes.top() << ", __meta_escape_pack(sizeof...(" << PackName->getName().str() << "), " << code << "...)";
		else
			escapes.top() << ", " << code;
		return true;
	}

	struct EscapeRAIIObject {
		QuasiQuoteRewriter& visitor;
		EscapeRAIIObject(QuasiQuoteRewriter& visitor) : visitor(visitor) {
			assert(visitor.qqNesting.top() && "escapes are valid only within quasi-quotes");
			visitor.qqNesting.push(0);
		}
		~EscapeRAIIObject() { visitor.qqNesting.pop(); }
	};

	Sema*							Actions;
	Rewriter						Rewrite;
	std::stack<std::ostringstream>	escapes;
	std::stack<unsigned>			totalEscapes;
	std::stack<unsigned>			qqNesting;
	std::stack<ParentMap*>			PMs;
};


class StageAssembler : public ASTConsumer, public StageNestingVisitor<StageAssembler> {
public:
	StageAssembler(SourceManager& manager, const LangOptions& options) :
		SM(manager), maxStageNesting(0) {
		stmtIndentation = PrintingPolicy(options).Indentation;
	}

	void HandleTranslationUnit(ASTContext &Context) override
		{ TraverseDecl(Context.getTranslationUnitDecl()); }

	bool VisitUnaryInline(UnaryOperator *O) { return HandleInline(O->getSubExpr()); }
	bool VisitInlineDecl(InlineDecl *D) { return HandleInline(D->getExpr()); }

    bool VisitExecuteStmt(ExecuteStmt *S) { return HandleExecute(S->getStmt()); }
	bool VisitExecuteDecl(ExecuteDecl *D) { return HandleExecute(D->getStmt()); }
	
	bool VisitDefDecl(DefDecl *D) {
		if (!qqNesting && D && CheckAndUpdateMaxStageNesting()) {
			std::string str;
			raw_string_ostream os(str);
			
			D->print(os);
			defs << os.str().substr(2);	//skip the initial .@
		}
		return true;
	}

	std::string AssembleStageCode(void)  {
		std::ostringstream ss;
		ss	<< "//meta compiler extern funcs\n"
			<< "extern void  __meta_inline(void*);\n"
			<< "extern void* __meta_qq(const char*, unsigned, ...);\n"
			<< "extern void* __meta_escape_pack(unsigned, ...);\n"
			<< "extern void* __meta_context();\n"
			<< "\n//stage defs\n" << defs.str()
			<< "\n//stage program\nint main() {\n" << stmts.str();
		indentStream(ss) << "return 0;\n}\n";
		return ss.str();
	}

	unsigned getMaxStageNesting() const { return maxStageNesting; }

private:
	bool HandleInline(Stmt* S) { return HandleInline(to_string(S)); }
	bool HandleInline(const std::string& code) {
		if (!qqNesting && CheckAndUpdateMaxStageNesting())
			indentStream(stmts) << "__meta_inline(" << code << ");\n";
		return true;
	}

	bool HandleExecute(Stmt *S) {
		if (!qqNesting && S && CheckAndUpdateMaxStageNesting()) {
			bool isExpr = isa<Expr>(S);
			if (isExpr)
				indentStream(stmts);
			stmts << to_string(S, stmtIndentation);
			if (isExpr)
				stmts << ";\n";
		}
		return true;
	}

	template<typename T>
	T& indentStream(T& os) {
		for (unsigned i = 0; i < stmtIndentation; ++i)
			os << "  ";
		return os;
	}

	bool CheckAndUpdateMaxStageNesting() {
		if (stageNesting > maxStageNesting) {
			maxStageNesting = stageNesting;
			defs.str(std::string());
			stmts.str(std::string());
		}
		return stageNesting == maxStageNesting;
	}

	SourceManager&		SM;
	unsigned			maxStageNesting;
	unsigned			stmtIndentation;
	std::ostringstream	defs;
	std::ostringstream	stmts;
};

//===----------------------------------------------------------------------===//
// Main driver
//===----------------------------------------------------------------------===//

static void LLVMErrorHandler(void *UserData, const std::string &Message,
                             bool GenCrashDiag) {
	DiagnosticsEngine &Diags = *static_cast<DiagnosticsEngine*>(UserData);

	Diags.Report(diag::err_fe_error_backend) << Message;

	// Run the interrupt handlers to make sure any special cleanups get done, in
	// particular that we remove files registered with RemoveFileOnSignal.
	sys::RunInterruptHandlers();

	// We cannot recover from llvm errors.  When reporting a fatal error, exit
	// with status 70 to generate crash diagnostics.  For BSD systems this is
	// defined as an internal software error.  Otherwise, exit with status 1.
	exit(GenCrashDiag ? 70 : 1);
}

#ifdef LINK_POLLY_INTO_TOOLS
namespace polly {
void initializePollyPasses(PassRegistry &Registry);
}
#endif

static ExecutionEngine *
createExecutionEngine(std::unique_ptr<llvm::Module> M, std::string *ErrorStr) {
	return EngineBuilder(std::move(M)).setEngineKind(EngineKind::Either)
		.setErrorStr(ErrorStr).create();
}

std::string dataLayoutString;

static bool Execute(std::unique_ptr<llvm::Module> Mod) {
	if (!Mod)
		return false;
	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();

	llvm::Module &M = *Mod;
#ifdef _WIN32
	M.setTargetTriple(sys::getProcessTriple() + "-elf");
	M.setDataLayout(dataLayoutString);
#endif

	std::string error;
	std::unique_ptr<ExecutionEngine> EE(createExecutionEngine(std::move(Mod), &error));
	bool result = false;
	if (!EE)
		errs() << "unable to make execution engine: " << error << "\n";
	else if (Function *main = M.getFunction("main")) {
		EE->finalizeObject();
		EE->runStaticConstructorsDestructors(M, false);
		result = !EE->runFunctionAsMain(main, std::vector<std::string>(1, M.getModuleIdentifier()), nullptr);
		EE->runStaticConstructorsDestructors(M, true);
	}
	else
		errs() << "'main' function not found in module.\n";
	return result;
}

void AddIncludePath(CompilerInstance *C, llvm::StringRef path) {
	HeaderSearchOptions& headerOpts = C->getHeaderSearchOpts();
	for (auto I = headerOpts.UserEntries.begin(), E = headerOpts.UserEntries.end(); I != E; ++I)
		if (I->Path == path)
			return;

	headerOpts.AddPath(path, frontend::Quoted, false, true);
	Preprocessor& PP = C->getPreprocessor();
	ApplyHeaderSearchOptions(PP.getHeaderSearchInfo(), headerOpts, PP.getLangOpts(), PP.getTargetInfo().getTriple());
}

bool ResetCompiler(CompilerInstance *C, ArrayRef<const char *> Argv) {
	IntrusiveRefCntPtr<DiagnosticIDs> DiagID(new DiagnosticIDs());
	IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
	TextDiagnosticBuffer *DiagsBuffer = new TextDiagnosticBuffer;
	DiagnosticsEngine Diags(DiagID, &*DiagOpts, DiagsBuffer);
	if (!CompilerInvocation::CreateFromArgs(C->getInvocation(), Argv.begin(), Argv.end(), Diags))
		return false;
	C->createDiagnostics();
	DiagsBuffer->FlushDiagnostics(C->getDiagnostics());

	std::shared_ptr<clang::TargetOptions> pto = std::make_shared<clang::TargetOptions>();
	pto->Triple = sys::getDefaultTargetTriple() + "-elf";
	TargetInfo *pti = TargetInfo::CreateTargetInfo(C->getDiagnostics(), pto);
	if (dataLayoutString.empty())
		dataLayoutString = pti->getDataLayoutString();
	C->setTarget(pti);

	C->createFileManager();
	C->createSourceManager(C->getFileManager());
	C->createPreprocessor(clang::TU_Complete);
	C->createASTContext();

	std::vector<llvm::StringRef> includes{
		"C:/Users/John/Desktop/MetaCPP/llvm/include",
		"C:/Users/John/Desktop/MetaCPP/build/include",
		"C:/Users/John/Desktop/MetaCPP/llvm/tools/clang/include/",
		"C:/Users/John/Desktop/MetaCPP/build/tools/clang/include"
	};
	for (auto& include : includes)
		AddIncludePath(C, include);

	return true;
}

void Parse(CompilerInstance *C, ASTConsumer *consumer) {
	DiagnosticConsumer& DC = C->getDiagnosticClient();
	Preprocessor& PP = C->getPreprocessor();
	DC.BeginSourceFile(C->getLangOpts(), &PP);
	PP.getBuiltinInfo().initializeBuiltins(PP.getIdentifierTable(),
                                           PP.getLangOpts());
	ParseAST(PP, consumer, C->getASTContext());
	DC.EndSourceFile();
}

FileID SetInputCode(CompilerInstance *C, const std::string &sourceName, const char * sourceText) {
	std::unique_ptr<MemoryBuffer> buf = MemoryBuffer::getMemBuffer(sourceText);
	const FileEntry *source = C->getFileManager().getVirtualFile(sourceName, buf->getBufferSize(), 0);
  
	SourceManager& SM = C->getSourceManager();
	SM.overrideFileContents(source, std::move(buf));
	FileID file = SM.createFileID(source, SourceLocation(), clang::SrcMgr::C_User);
	SM.setMainFileID(file);

	std::vector<FrontendInputFile>& inputs = C->getFrontendOpts().Inputs;
	inputs.clear();
	inputs.push_back(FrontendInputFile(sourceName, IK_CXX));
	return file;
}

int meta_cc1_main(ArrayRef<const char *> Argv, const char *Argv0, void *MainAddr) {
	GlobalArgv = Argv;
	std::unique_ptr<CompilerInstance> Clang(new CompilerInstance());

	// Register the support for object-file-wrapped Clang modules.
	auto PCHOps = Clang->getPCHContainerOperations();
	PCHOps->registerWriter(make_unique<ObjectFilePCHContainerWriter>());
	PCHOps->registerReader(make_unique<ObjectFilePCHContainerReader>());

	// Initialize targets first, so that --version shows registered targets.
	InitializeAllTargets();
	InitializeAllTargetMCs();
	InitializeAllAsmPrinters();
	InitializeAllAsmParsers();

#ifdef LINK_POLLY_INTO_TOOLS
	PassRegistry &Registry = *PassRegistry::getPassRegistry();
	polly::initializePollyPasses(Registry);
#endif

	if (!ResetCompiler(Clang.get(), Argv))
		return 1;

	LangOps = Clang->getLangOpts();

	// Infer the builtin include path if unspecified.
	if (Clang->getHeaderSearchOpts().UseBuiltinIncludes &&
		Clang->getHeaderSearchOpts().ResourceDir.empty())
	Clang->getHeaderSearchOpts().ResourceDir =
		CompilerInvocation::GetResourcesPath(Argv0, MainAddr);

	// Set an error handler, so that any LLVM backend diagnostics go through our
	// error handler.
	install_fatal_error_handler(LLVMErrorHandler,
									static_cast<void*>(&Clang->getDiagnostics()));

	SourceManager& SM = Clang->getSourceManager();  
	const FileEntry *FileIn = Clang->getFileManager().getFile(Clang->getFrontendOpts().Inputs.front().getFile());
	FileID mainFile = SM.createFileID(FileIn, SourceLocation(), clang::SrcMgr::C_User);
	SM.setMainFileID(mainFile);
 
	std::string transformedMain;	//this should be alive for the entire staging loop
	while(true) {
		StageAssembler assembler(Clang->getSourceManager(), Clang->getLangOpts());
		Parse(Clang.get(), &assembler);
		bool enable_runtime_debugging = 0;
		if (enable_runtime_debugging)
			Clang.get()->getASTContext().getTranslationUnitDecl()->print(errs(), 0, true);
		if (unsigned nesting = assembler.getMaxStageNesting()) {
			std::string stageCode = assembler.AssembleStageCode();
			//errs() << "\n---------------- STAGE ----------------\n" << stageCode;

			std::unique_ptr<CompilerInstance> MetaCompiler(new CompilerInstance());
			ResetCompiler(MetaCompiler.get(), Argv);
			SetInputCode(MetaCompiler.get(), "stage.cpp", stageCode.c_str());

			QuasiQuoteRewriter stageRewriter(MetaCompiler.get());
			remove_fatal_error_handler();
			install_fatal_error_handler(LLVMErrorHandler, static_cast<void*>(&MetaCompiler->getDiagnostics()));
			Parse(MetaCompiler.get(), &stageRewriter);

			std::string transformedStage;	//this should be alive until the stage is over
			if (const RewriteBuffer *RewriteBuf = stageRewriter.getRewriteBufferFor(mainFile)) {
				transformedStage.assign(RewriteBuf->begin(), RewriteBuf->end());
				errs() << "\n---------------- STAGE ----------------\n" << transformedStage;
				ResetCompiler(MetaCompiler.get(), Argv);
				SetInputCode(MetaCompiler.get(), "transformed_stage.cpp", transformedStage.c_str());
			}

			DeclContextMarker contextMarker;
			contextMarker.HandleTranslationUnit(MetaCompiler->getASTContext());

			std::unique_ptr<CodeGenAction> Act(new EmitLLVMOnlyAction());
			bool Success = MetaCompiler->ExecuteAction(*Act) && Execute(std::move(Act->takeModule()));
			if (!Success)
				return 1;

			StageResultRewriter mainRewriter(Clang.get(), nesting);
			mainRewriter.HandleTranslationUnit(Clang->getASTContext());

			if (const RewriteBuffer *RewriteBuf = mainRewriter.getRewriteBufferFor(mainFile))
				transformedMain.assign(RewriteBuf->begin(), RewriteBuf->end());
			else {
				std::string str;
				raw_string_ostream os(str);
				Clang.get()->getASTContext().getTranslationUnitDecl()->print(os, 0, true);
				transformedMain = os.str();
			}
			//errs() << "\n------------- STAGE RESULT ------------\n" << transformedMain;

			ResetCompiler(Clang.get(), Argv);
			mainFile = SetInputCode(Clang.get(), "transformed_main.cpp", transformedMain.c_str());
		}
		else {
			//final program here, just output
			if (transformedMain.empty())
				errs() << "no staging took place\n";
			else
				errs() <<"\n----------------- FINAL ----------------\n" << transformedMain;

			ExecuteCompilerInvocation(Clang.get());
			break;
		}
	}

	// If any timers were active but haven't been destroyed yet, print their
	// results now.  This happens in -disable-free mode.
	TimerGroup::printAll(errs());

	// Our error handler depends on the Diagnostics object, which we're
	// potentially about to delete. Uninstall the handler now so that any
	// later errors use the default handling behavior instead.
	remove_fatal_error_handler();

	// When running with -disable-free, don't do any destruction or shutdown.
	if (Clang->getFrontendOpts().DisableFree) {
		if (AreStatisticsEnabled() || Clang->getFrontendOpts().ShowStats)
			PrintStatistics();
		BuryPointer(std::move(Clang));
		return 0;
	}

	// Managed static deconstruction. Useful for making things like
	// -time-passes usable.
	llvm_shutdown();

	return 0;
}
