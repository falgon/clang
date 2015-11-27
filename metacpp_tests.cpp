// -- Statements --
void testStatements() {
	auto printer = [](const char*, ...){};
	.!(.<printer("Generated Hello World (runtime)\n")>.);
	 .!(.< .!(.<printer("Meta generator and nested QQs work!\n")>.) >.);
	.&void* expr = .<i < 10>.;
	.&void* stmt1 = .<break;>.;
	.&void* stmt2 = .<continue;>.;
	.&void* stmt3 = .<while(.~expr);>.;
	.!(.<
		for(unsigned i = 0; .~expr; ++i) {
			if (.~expr)
				.~stmt2;
			else
				switch(i) {
					default: .~stmt3; .~stmt1;
				}
			printer("i = %d\n", i);
		}
	>.);
}

// -- Functions & includes & variadic templates --
.@void* generateSimpleFunction(void* body) { return .< bool func() { .~body; } >.; }
.!(generateSimpleFunction(.<int var; return true;>.));

void .!(.<foo>.)() {}

.@#include <vector>
.@void* generateFunctionUsingVector(void* ret, void* name, const std::vector<void*>& args, void* body) {
	void *formals = nullptr;
	for (auto arg : args)
		formals = .<.~formals, .~arg>.;
	return .< typename .~ret .~name(typename .~formals) { .~body; } >.;
}
.@std::vector<void*> args{.<int x>., .<double y>.};
.!(generateFunctionUsingVector(.<bool>., .<func>., args, .<return true;>.));

.@#include <utility>
.@template<typename... Args> void* generateFunctionUsingVariadicArguments(void* ret, void* name, void* body, Args&&... args) {
	auto MakeFormals = [](const std::pair<void*, void*>& arg) { return .<typename .~(arg.first) .~(arg.second)>.; };
	return .< typename .~ret .~name(typename .~(MakeFormals(args))...) { .~body; } >.;
}
.!(generateFunctionUsingVariadicArguments(.<bool>., .<func1>., .<return true;>., std::make_pair(.<int>., .<x>.), std::make_pair(.<double>., .<y>.)));
.!(generateFunctionUsingVariadicArguments(.<void>., .<func2>., .<return;>.));

// -- Classes --
.@void* generateClassMembers(void* ClassName) {
	return .<
		friend void foo();
		void f(){}
		virtual typename .~ClassName* g();
		virtual void pure() = 0;
		typename .~ClassName(){}
		explicit typename .~ClassName(int a) : typename Base(1), x(a) {}
		~.~ClassName(){}
	>.;
}

.@void* generateMemberPointerFunctionCalls(void* ClassName) {
	void* func = .<g>.;
	void* ptr = .<this>.;
	void* obj = .<*this>.;
	void* call1 = .<((.~ptr)->*(&.~ClassName::.~func))()>.;
	void* call2 = .<((.~obj).*(&.~ClassName::.~func))()>.;
	void* call3 = .<(.~ptr)->.~func()>.;
	return .<.~call1; .~call2; .~call3;>.;
}

struct Base {
	Base(){}
	Base(int){}
};
class ClassWithGeneratedMembers : Base {
	int x;
	.!(generateClassMembers(.<typename ClassWithGeneratedMembers>.));
	void func() { .!(generateMemberPointerFunctionCalls(.<ClassWithGeneratedMembers>.)); }
};

.@void* generateClass(void* member1, void* member2, void* member3) {
	return .<
		class X {
			int a;
			.~member1;
			int b;
			.~member2;
			int c;
			.~member3;
		};
	>.;
}
.!(generateClass(.<void f(){}>., .<void g(){}>., .<int x;>.));

// -- Namespaces & qualified ids & using-- 
.@void* generateNamespace(void* body) { return .< namespace ns { .~body; } >.; }
.!(generateNamespace(.<void funcInNamespace(){} class Z{}; namespace nested { class Nested{}; }>.));

.@void* generateUsingDirective(void* oneNs, void* otherNs, void* func) { 
	return .<
		using namespace .~oneNs;
		using ns::.~func;
		.~otherNs;
	>.;
}
.!(generateUsingDirective(.<ns>., .<using namespace ns::nested; using ns::Z;>., .<funcInNamespace>.));

.@void* generateQualifiedId(void* innerNs, void* name) { return .<ns::.~innerNs::.~name>.; }
typename .!(generateQualifiedId(.<nested>., .<Nested>.)) QualifiedNamespaceDecl;

// -- Misc declarations --
.@void* generateFwdDeclarations(void* decl) { return .<class FwdClassDecl; void f(void); .~decl;>.;}
.!(generateFwdDeclarations(.<struct FwdStructDecl; enum FwdEnumDecl;>.));

.@void* generateTypedef() { return .<typedef int MyInt;>.;}
.!(generateTypedef());

.@void* generateAlias() { return .<using MyDouble = double;>.;}
.!(generateAlias());

// -- Lambdas -- 
.@template<typename... Args>
  void* generateLabdaWithVariadicCaptureList(Args&&... args) { return .<[&.~args...](){}>.; } //TODO: capture applied only in the first arg
.@void* generateLambdaCapture(void* capture) { return .<[&.~capture](int x) { .~capture += x; }>.; }
int testGeneratedLambda() {
	int sum = 0;
	int array[] = {1, 2, 3, 4, 5};
	for (unsigned i = 0; i < sizeof(array)/sizeof(*array); ++i)
		(.!(generateLambdaCapture(.<sum>.)))(array[i]);	//TODO: check why syntax does not allow it without parenthesis (takes it as a decl)

	int a, b;
	(.!(generateLabdaWithVariadicCaptureList(.<a>., .<b>.)))();
	return sum;
}

//-- Templates --
.@void* generateTemplateClass(void* member) { return .< template<typename T> struct Y { T val; .~member; }; >.; }
.!(generateTemplateClass(.<void getVal(){ return val; }>.));

.@void* generateTemplateFunction(void* body) { return .< template<typename T> bool template_func() { T val; .~body; } >.; }
.!(generateTemplateFunction(.<return val;>.));

.!(.<template<typename T> struct Template{ using Type = int; static const int x = 0; };>.);
.@void * makeUnqualifiedTemplate(void *templateId, void* type) { return .< ::template .~templateId<typename .~type> >.; }
typename .!(makeUnqualifiedTemplate(.<Template>., .<int>.)) UnqualifiedTemplateVar1;
typename ::template .!(.<Template>.)<int> UnqualifiedTemplateVar2;

.@void * makeTemplateType(void* type) { return .< ns::template QualifiedTemplate< typename .~type> >.; }
namespace ns { template<typename T> class QualifiedTemplate {}; }
typename .!(makeTemplateType(.<int>.)) QualifiedTemplateVar;

typename .!(.<typename ::template Template<int>::Type >.) TemplateValue = .!(.<::template Template<int>::x >.);
.!(.<template <class T> class A : public ::template Template<T> { using ::template Template<T>::x; };>.);

//-- Reflection & context  dependent --
.@#include "clang/void/DeclCXX.h"
.@void* generateAttributeFuncs(void *D) {
	using namespace clang;
	CXXRecordDecl *Decl = (CXXRecordDecl *)D;
	void* result = nullptr;
	for (const auto* field : Decl->fields()) {
		const std::string type = field->getType().getAsString();
		const std::string name = field->getName().str();
		result = .<.~result;
			typename .~type .~(std::string("get") + name)(void) const { return .~name; }
			void .~(std::string("set") + name)(typename .~type .~name) { this->.~name = .~name; }
		>.
	}
	return result;
}

class Point {
private:
	int x, y;
public:
	.!(generateAttributeFuncs(__meta_context()));
};

//-- Power example --
.@void* ExpandPower(const void* x, unsigned n) {
	if (n == 0)
		return .<1>.;
	else if (n == 1)
		return x;
	else
		return .< .~x * .~ExpandPower(x, n - 1) >.;
}
.@void* MakePower(void* name, unsigned n){
	void* expanded = ExpandPower(.<x>., n);
	return .<int .~name (int x) { return .~expanded; }>.;
}
.!(MakePower(.<power3>., 3));