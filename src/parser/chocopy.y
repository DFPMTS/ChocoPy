%locations
%define api.location.type {::parser::Location}

%{
#define YYLLOC_DEFAULT(Cur, Rhs, N)
#include <cstdio>
#include <cstdarg>
#include <vector>
#include <string>
#include <iostream>
#include <algorithm>

#include "chocopy_parse.hpp"
#include "chocopy_ast.hpp"

using ::parser::Location;

/* external functions from lex */
extern void yyrestart(FILE*);
extern int yylex();
extern int yyparse();
extern FILE* yyin;

/* the program, the root of AST
* all information is stored in ROOT
* The AST (a tree) structure is held by (smart) pointers. 
*/
std::unique_ptr<::parser::Program> ROOT = std::make_unique<::parser::Program>(Location());

/* error reporting */
void yyerror(const char *s);

/* append item to the end of LIST. Then returns LIST. */
/* this is a handy helper function. */
template<typename T, typename X>
T* combine(T* list, X *item) {
    list->emplace_back(item);
    return list;
}
using VecDecl = std::vector<std::unique_ptr<::parser::Decl>>;
using VecStmt = std::vector<std::unique_ptr<::parser::Stmt>>;
using VecTypedVar = std::vector<std::unique_ptr<::parser::TypedVar>>;
using VecExpr = std::vector<std::unique_ptr<::parser::Expr>>;
using PairVecDeclStmt = std::pair<std::vector<std::unique_ptr<::parser::Decl>> *,std::vector<std::unique_ptr<::parser::Stmt>> *>;
using PtrVecDecl = std::vector<std::unique_ptr<::parser::Decl>>*;
using PtrVecStmt = std::vector<std::unique_ptr<::parser::Stmt>>*;
using PtrVecTypedVar = std::vector<std::unique_ptr<::parser::TypedVar>>*;
using PtrVecExpr = std::vector<std::unique_ptr<::parser::Expr>>*;
%}

/* all possible types of semantic value */
/* check https://www.gnu.org/software/bison/manual/html_node/Union-Decl.html */
%union {
  char *raw_str;
  int raw_int;
  ::parser::Stmt *PtrStmt;
  ::parser::Decl *PtrDecl;
  ::parser::AssignStmt *PtrAssignStmt;
  ::parser::BinaryExpr *PtrBinaryExpr;
  ::parser::BoolLiteral *PtrBoolLiteral;
  ::parser::CallExpr *PtrCallExpr;
  ::parser::ClassDef *PtrClassDef;
  ::parser::ClassType *PtrClassType;
  ::parser::Expr *PtrExpr;
  ::parser::ExprStmt *PtrExprStmt;
  ::parser::ForStmt *PtrForStmt;
  ::parser::FuncDef *PtrFuncDef;
  ::parser::GlobalDecl *PtrGlobalDecl;
  ::parser::Ident *PtrIdent;
  ::parser::IfExpr *PtrIfExpr;
  ::parser::IndexExpr *PtrIndexExpr;
  ::parser::IntegerLiteral *PtrIntegerLiteral;
  ::parser::ListExpr *PtrListExpr;
  ::parser::ListType *PtrListType;
  ::parser::Literal *PtrLiteral;
  ::parser::MemberExpr *PtrMemberExpr;
  ::parser::MethodCallExpr *PtrMethodCallExpr;
  ::parser::Node *PtrNode;
  ::parser::NoneLiteral *PtrNoneLiteral;
  ::parser::NonlocalDecl *PtrNonlocalDecl;
  ::parser::ReturnStmt *PtrReturnStmt;
  ::parser::StringLiteral *PtrStringLiteral;
  ::parser::TypeAnnotation *PtrTypeAnnotation;
  ::parser::TypedVar *PtrTypedVar;
  ::parser::UnaryExpr *PtrUnaryExpr;
  ::parser::VarDef *PtrVarDef;
  ::parser::WhileStmt *PtrWhileStmt;
  ::parser::IfStmt *PtrIfStmt;
  std::vector<std::unique_ptr<::parser::Decl>> *PtrListDecl;
  std::vector<std::unique_ptr<::parser::Stmt>> *PtrListStmt;
  std::vector<std::unique_ptr<::parser::TypedVar>> *PtrListTypedVar;
  std::vector<std::unique_ptr<::parser::Expr>> *PtrExprList;
  std::pair<std::vector<std::unique_ptr<::parser::Decl>> *,std::vector<std::unique_ptr<::parser::Stmt>> *>* PtrFuncBody;
}


/* declare tokens and their type */
/* check https://www.gnu.org/software/bison/manual/html_node/Token-Decl.html */

/*
* You can delete, add, and modify the below at your convenience.
*/

%token <raw_int> TOKEN_INTEGER
%token <raw_str> TOKEN_IDENTIFIER
%token <raw_str> TOKEN_STRING
%token <raw_str> TOKEN_IDSTRING
%token TOKEN_TRUE
%token TOKEN_FALSE
%token TOKEN_AND
%token TOKEN_BREAK
%token TOKEN_DEF
%token TOKEN_ELIF
%token TOKEN_ELSE
%token TOKEN_FOR
%token TOKEN_IF
%token TOKEN_NOT
%token TOKEN_OR
%token TOKEN_RETURN
%token TOKEN_WHILE
%token TOKEN_NONE
%token TOKEN_AS
%token TOKEN_CLASS
%token TOKEN_GLOBAL
%token TOKEN_IN
%token TOKEN_IS
%token TOKEN_NONLOCAL
%token TOKEN_PASS
%token TOKEN_plus
%token TOKEN_minus
%token TOKEN_star
%token TOKEN_slash
%token TOKEN_percent
%token TOKEN_less
%token TOKEN_greater
%token TOKEN_lessequal
%token TOKEN_greaterequal
%token TOKEN_equalequal
%token TOKEN_exclaimequal
%token TOKEN_equal
%token TOKEN_l_paren
%token TOKEN_r_paren
%token TOKEN_l_square
%token TOKEN_r_square
%token TOKEN_comma
%token TOKEN_colon
%token TOKEN_period
%token TOKEN_rarrow
%token TOKEN_INDENT
%token TOKEN_DEDENT
%token TOKEN_NEWLINE
%token TOKEN_UNRECOGNIZED

%type <PtrStmt> stmt simple_stmt
%type <PtrIfStmt> elif_list
%type <PtrListDecl> top_level_decl class_body 
%type <PtrListStmt> stmt_list block opt_stmt_list
%type <PtrListTypedVar> typed_var_list opt_typed_var_list
%type <PtrClassDef> class_def
%type <PtrGlobalDecl> global_decl
%type <PtrTypedVar> typed_var
%type <PtrTypeAnnotation> type func_return_type
%type <PtrExpr> expr cexpr target binary_expr
%type <PtrExprList> expr_list opt_expr_list 
%type <PtrIndexExpr> index_expr
%type <PtrMemberExpr> member_expr
%type <PtrLiteral> literal
%type <PtrIdent> identifier
%type <PtrVarDef> var_def
%type <PtrFuncDef> func_def
%type <PtrNonlocalDecl> nonlocal_decl
%type <PtrAssignStmt> assign_stmt
%type <PtrDecl> single_program_decl single_func_decl single_class_decl
%type <PtrFuncBody> func_body

/* the destructor is called when error happends */
/* you don't need to modify the code */
/* check https://www.gnu.org/software/bison/manual/html_node/Destructor-Decl.html */
%destructor { } <raw_int>
%destructor { free($$); } <raw_str>
%destructor { delete $$; } <*>

/* you may define associativity and precedence here */
/* check https://www.gnu.org/software/bison/manual/html_node/Precedence-Decl.html */
%right TOKEN_IF TOKEN_ELSE
%left TOKEN_OR
%left TOKEN_AND
%left TOKEN_NOT
%nonassoc TOKEN_equalequal TOKEN_exclaimequal TOKEN_greater TOKEN_greaterequal TOKEN_less TOKEN_lessequal TOKEN_IS
%left TOKEN_plus TOKEN_minus
%left TOKEN_star TOKEN_slash TOKEN_percent
%left UMINUS
%right TOKEN_period TOKEN_comma TOKEN_l_square TOKEN_r_square

%start program

%%
/* write grammar rule here! */

/* The start symbol of your grammar */
/* The rule is not complete(nor sound). You can rewrite and add some rules. */
/* 喜报：我们不再对 JSON 中 "Locaton" 项计分，因此你可以选择不计算每个 symbol 的 Location。程序也不会输出关于 Location 的信息。
 * 你可以添加 __PARSER_PRINT_LOCATION 的宏定义以恢复 Location 的输出。
 * 你只需用 Location() 新建一个空 Location 传入构造函数。 
 */
program : top_level_decl opt_stmt_list {
                ROOT = std::move(std::make_unique<::parser::Program>(Location(), $1, $2));
            }
        | stmt_list {
                ROOT = std::move(std::make_unique<::parser::Program>(Location(), new VecDecl(),$1));
            }
        ;
/* Entry point to declerations */
top_level_decl  : single_program_decl { 
                        $$ = new std::vector<std::unique_ptr<::parser::Decl>>(); 
                        $$->emplace_back($1);
                    }
                | top_level_decl single_program_decl { $$=combine($1,$2); }
                ;

single_program_decl : var_def
                    | func_def
                    | class_def
                    ;

class_def   : TOKEN_CLASS identifier[name] TOKEN_l_paren identifier[parent] TOKEN_r_paren TOKEN_colon TOKEN_NEWLINE TOKEN_INDENT class_body[body] TOKEN_DEDENT {
                    $$=new ::parser::ClassDef(Location(),$name,$parent,$body);
                }    
            ;

class_body  : single_class_decl             { 
                    $$=new VecDecl(); 
                    $$->emplace_back($1);
                }       
            | class_body single_class_decl  { 
                    $$=$1;
                    $$->emplace_back($2); 
                }
            | TOKEN_PASS TOKEN_NEWLINE {
                    $$=new VecDecl(); 
                }
            ;

single_class_decl   : var_def
                    | func_def
                    ;

func_def    : TOKEN_DEF identifier[name] TOKEN_l_paren  opt_typed_var_list[args] TOKEN_r_paren func_return_type[returntype] TOKEN_colon TOKEN_NEWLINE TOKEN_INDENT func_body[body] TOKEN_DEDENT {
                    std::reverse($body->first->begin(),$body->first->end());
                    $$=new ::parser::FuncDef(Location(),$name,$args,$returntype,$body->first,$body->second);
                    delete($body);
                }
            ;

func_return_type    :  { $$=nullptr; }
                    | TOKEN_rarrow type { $$=$2; }

func_body   : single_func_decl func_body { 
                    $$=$2;
                    $$->first->emplace_back($1);
                }
            | stmt_list {
                    $$=new PairVecDeclStmt(new VecDecl(),$1);
                }
            ;

single_func_decl    : global_decl
                    | nonlocal_decl
                    | func_def
                    | var_def
                    ;

var_def : typed_var TOKEN_equal literal TOKEN_NEWLINE { $$=new ::parser::VarDef(Location(),$1,$3); }
        ;

typed_var   : identifier TOKEN_colon type { $$=new ::parser::TypedVar(Location(),$1,$3); }
            ;

opt_typed_var_list  : { $$=new VecTypedVar();}
                    | typed_var_list
                    ;

typed_var_list  : typed_var { 
                        $$=new VecTypedVar;
                        $$->emplace_back($1);
                    }
                | typed_var_list TOKEN_comma typed_var { $$=combine($1,$3); }
                ;


type    : TOKEN_IDENTIFIER                      { $$=new ::parser::ClassType(Location(),std::string($1)); }
        | TOKEN_IDSTRING                        { $$=new ::parser::ClassType(Location(),std::string($1)); }
        | TOKEN_l_square type TOKEN_r_square    { $$=new ::parser::ListType(Location(),$2); }
        ;

global_decl : TOKEN_GLOBAL identifier TOKEN_NEWLINE         { $$=new ::parser::GlobalDecl(Location(),$2); }
            ;

nonlocal_decl   : TOKEN_NONLOCAL identifier TOKEN_NEWLINE   { $$=new ::parser::NonlocalDecl(Location(),$2); }
                ;

opt_stmt_list   : { $$=new VecStmt(); }
                | stmt_list { $$=$1; }
                ;

stmt_list   : stmt {
                    $$ = new std::vector<std::unique_ptr<::parser::Stmt>>();
                    // if ($1->kind!="PassStmt")
                        $$->emplace_back($1);
                }
            | stmt_list stmt { 
                    $$=$1; 
                    // if ($2->kind!="PassStmt")
                        $$->emplace_back($2);
                }
            ;
stmt: simple_stmt TOKEN_NEWLINE { $$ = $1; }
    | TOKEN_IF expr[cond] TOKEN_colon block[then] TOKEN_ELSE TOKEN_colon block[else]    { $$=new ::parser::IfStmt(Location(),$cond,$then,$else);}
    | TOKEN_IF expr[cond] TOKEN_colon block[then]                                       { $$=new ::parser::IfStmt(Location(),$cond,$then);}
    | TOKEN_IF expr[cond] TOKEN_colon block[then] elif_list[elif]                       { $$=new ::parser::IfStmt(Location(),$cond,$then,$elif); }
    | TOKEN_WHILE expr[cond] TOKEN_colon block[do]                                      { $$=new ::parser::WhileStmt(Location(),$cond,$do); }
    | TOKEN_FOR identifier[i] TOKEN_IN expr[list] TOKEN_colon block[do]                 { $$=new ::parser::ForStmt(Location(),$i,$list,$do); }
    ;

elif_list   : TOKEN_ELIF expr[cond] TOKEN_colon block[then]                                     { $$=new ::parser::IfStmt(Location(),$cond,$then); }
            | TOKEN_ELIF expr[cond] TOKEN_colon block[then] TOKEN_ELSE TOKEN_colon block[else]  { $$=new ::parser::IfStmt(Location(),$cond,$then,$else); }            
            | TOKEN_ELIF expr[cond] TOKEN_colon block[then] elif_list[elif]                     { $$=new ::parser::IfStmt(Location(),$cond,$then,$elif); }
            ;

simple_stmt : expr              { $$ = new parser::ExprStmt(Location(), $1); } 
            | TOKEN_PASS        { $$=new ::parser::PassStmt(Location()); }
            | TOKEN_RETURN expr { $$=new ::parser::ReturnStmt(Location(), $2); }
            | TOKEN_RETURN      { $$=new ::parser::ReturnStmt(Location()); }
            | assign_stmt       {                     
                    std::reverse($1->targets.begin(),$1->targets.end()); 
                    $$=$1;
                }
            ;

assign_stmt : target TOKEN_equal expr { $$=new ::parser::AssignStmt(Location(), $1, $3); }
            | target TOKEN_equal assign_stmt { 
                    $$=$3;
                    $$->targets.emplace_back($1);
                }
            ;

target  : identifier
        | member_expr 
        | index_expr
        ;

block   : TOKEN_NEWLINE TOKEN_INDENT stmt_list TOKEN_DEDENT { $$=$3; }

expr: expr[then] TOKEN_IF expr[cond] TOKEN_ELSE expr[else] { 
            $$=new ::parser::IfExpr(Location(),$cond,$then,$else); 
        }
    | cexpr { $$=$1; }
    | TOKEN_NOT expr                   { $$=new ::parser::UnaryExpr(Location(),std::string("not"),$2); }
    | expr TOKEN_AND expr   { $$=new ::parser::BinaryExpr(Location(),$1,std::string("and"),$3); }
    | expr TOKEN_OR expr    { $$=new ::parser::BinaryExpr(Location(),$1,std::string("or"),$3); }            
    ;

cexpr   : literal { $$ = $1; }
        | identifier 
        | TOKEN_l_square opt_expr_list TOKEN_r_square   { $$=new ::parser::ListExpr(Location(),$2); }
        | TOKEN_l_paren expr TOKEN_r_paren              { $$=$2; }
        | member_expr
        | index_expr
        | member_expr TOKEN_l_paren opt_expr_list TOKEN_r_paren { $$=new ::parser::MethodCallExpr(Location(),$1,$3); }
        | identifier TOKEN_l_paren opt_expr_list TOKEN_r_paren  { $$=new ::parser::CallExpr(Location(),$1,$3); }
        | binary_expr
        | TOKEN_minus cexpr %prec UMINUS { $$=new ::parser::UnaryExpr(Location(),std::string("-"),$2); }
        ;

expr_list   : expr {
                    $$ = new VecExpr();
                    $$->emplace_back($1);
                }
            | expr_list TOKEN_comma expr {
                    $$=$1;
                    $$->emplace_back($3);
                }
            ;

opt_expr_list   : {$$=new VecExpr();} 
                | expr_list 
                ;

member_expr : cexpr TOKEN_period identifier { $$=new ::parser::MemberExpr(Location(),$1,$3); }   
            ;

index_expr  : cexpr TOKEN_l_square expr TOKEN_r_square { $$=new ::parser::IndexExpr(Location(),$1,$3); }
            ;

binary_expr : cexpr TOKEN_plus cexpr            {$$=new ::parser::BinaryExpr(Location(),$1,std::string("+"),$3);}
            | cexpr TOKEN_minus cexpr           {$$=new ::parser::BinaryExpr(Location(),$1,std::string("-"),$3);}
            | cexpr TOKEN_star cexpr            {$$=new ::parser::BinaryExpr(Location(),$1,std::string("*"),$3);}
            | cexpr TOKEN_slash cexpr           {$$=new ::parser::BinaryExpr(Location(),$1,std::string("//"),$3);}
            | cexpr TOKEN_percent cexpr         {$$=new ::parser::BinaryExpr(Location(),$1,std::string("%"),$3);}
            | cexpr TOKEN_equalequal cexpr      {$$=new ::parser::BinaryExpr(Location(),$1,std::string("=="),$3);}
            | cexpr TOKEN_exclaimequal cexpr    {$$=new ::parser::BinaryExpr(Location(),$1,std::string("!="),$3);}
            | cexpr TOKEN_lessequal cexpr       {$$=new ::parser::BinaryExpr(Location(),$1,std::string("<="),$3);}
            | cexpr TOKEN_greaterequal cexpr    {$$=new ::parser::BinaryExpr(Location(),$1,std::string(">="),$3);}
            | cexpr TOKEN_less cexpr            {$$=new ::parser::BinaryExpr(Location(),$1,std::string("<"),$3);}
            | cexpr TOKEN_greater cexpr         {$$=new ::parser::BinaryExpr(Location(),$1,std::string(">"),$3);}
            | cexpr TOKEN_IS cexpr              {$$=new ::parser::BinaryExpr(Location(),$1,std::string("is"),$3);}
            ;

literal : TOKEN_NONE        {$$=new ::parser::NoneLiteral(Location());}
        | TOKEN_TRUE        {$$=new ::parser::BoolLiteral(Location(),true);}
        | TOKEN_FALSE       {$$=new ::parser::BoolLiteral(Location(),false);} 
        | TOKEN_INTEGER     {$$=new ::parser::IntegerLiteral(Location(),$1);}
        | TOKEN_STRING      {$$=new ::parser::StringLiteral(Location(),std::string($1));}
        | TOKEN_IDSTRING    {$$=new ::parser::StringLiteral(Location(),std::string($1));}
        ;


identifier  :   TOKEN_IDENTIFIER  {$$=new ::parser::Ident(Location(),std::string($1));}
            ;



%%

/** The error reporting function. */
void yyerror(const char *s) {
    /* This is just an example.
     * You can customize it as you like. */
    string info("Parsing error");
    auto error = std::make_unique<::parser::CompilerErr>(Location(), info, true);
    ROOT->errors->compiler_errors.emplace_back(std::move(error));
}

std::unique_ptr<::parser::Program> parse(const char* input_path) {
    if (input_path != NULL) {
        if (!(yyin = fopen(input_path, "r"))) {
            std::cerr << fmt::format("[ERR] Open input file {} failed.", input_path) << std::endl;
            exit(EXIT_FAILURE);
        }
    } else {
        yyin = stdin;
    }
    /* uncomment to see the middle process of Bison */
    /* yydebug = 1; */
    yyrestart(yyin);
    yyparse();
    return std::move(ROOT);
}
