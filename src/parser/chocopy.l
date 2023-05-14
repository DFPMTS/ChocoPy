%option noyywrap
%option yylineno
/* The prefix for imports in c syntax */
%{
/* For Indentation */
#include <stack>
#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <string>

#if __cplusplus > 199711L
#define register      // Deprecated in C++11.
#endif  // #if __cplusplus > 199711L

using namespace std;
std::stack<int> stack_indent;

#include <chocopy_parse.hpp>
#include "chocopy.tab.h"

#define MY_INT_MAX 2147483647
#define INIT_BUF_SIZE 1024

int toIndent=0,toDedent=0,IndentationError=0;
size_t buf_size=INIT_BUF_SIZE;
auto buf=make_shared<char[]>(INIT_BUF_SIZE);
/* use string s to temporarily store string literals */
string s;
/* distinguish IDSTRING and STRING, default value is -1 */
int is_IDSTRING;
int slen;
void count_indentation(const char *s);
%}

%x STRING

%x Content
%x EndOfLine
%x EndOfProgram
%x IndentationEnv

/* ChocoPy's string contains characters from ASCII 32-126, which corresponds to \x20-\x7e */

%%

%{
  /* Init indent stack_indent */
  if (stack_indent.empty()) {
    stack_indent.push(0);
  }
%}

<INITIAL>{
    [ \t]*(#[^\r\n]*)?(\r\n|\r|\n) { BEGIN(EndOfLine);}    
    [ \t]*/[^ \t\n\r#]  {count_indentation(yytext);  BEGIN(IndentationEnv);} 
    [ \t]*              {BEGIN(EndOfLine);}
}

<STRING>{
    \" {
        if(is_IDSTRING==2){
            return 0;
        }
        if(s.size()+10>=buf_size){
                buf_size=s.size()+10;
                buf=make_shared<char[]>(buf_size);
        }
        strcpy(buf.get(), s.c_str());
        yylval.raw_str=buf.get();        
        yyleng=slen;                
        BEGIN(Content);
        if(is_IDSTRING==1){
            return TOKEN_IDSTRING;
        }else{
            return TOKEN_STRING;
        }
    }
    [_a-zA-Z][_a-zA-Z0-9]* {
        is_IDSTRING=1;
        s+=std::string(yytext);
    }

    ([\x20-\x7e]{-}[\"\\])* {
        is_IDSTRING=0;
        s+=std::string(yytext);
    }

    \\n {
        is_IDSTRING=0;
        s+="\n";
    }
    \\t {
        is_IDSTRING=0;
        s+="\t";
    }
    \\\\ {
        is_IDSTRING=0;
        s+="\\";
    }
    \\\" {
        is_IDSTRING=0;
        s+="\"";
    }
    . {
        is_IDSTRING=2;
    }
}

<Content>{
    0|[1-9][0-9]* {
            long long x=0; int len= strlen(yytext);
            for(int i=0;i<len;++i){
                x=x*10+yytext[i]-'0';
                if(x>MY_INT_MAX){
                    return 0; /* */
                }
            }
            yylval.raw_int=x;     
            
            return TOKEN_INTEGER;
        }    
    \"(([\x20-\x7e]{-}[\"\\])|\\t|\\n|\\\\|\\\")*\" {
            slen=yyleng;
            s="";
            is_IDSTRING=-1;            
            yyless(1);
            BEGIN(STRING);                        
        }
    "True" {  return TOKEN_TRUE;}
    "False" {  return TOKEN_FALSE;}
    "and" { return TOKEN_AND;}
    "break" { return TOKEN_BREAK;}
    "def" { return TOKEN_DEF;}
    "elif" { return TOKEN_ELIF;}
    "else" { return TOKEN_ELSE;}
    "for" { return TOKEN_FOR;}
    "if" { return TOKEN_IF;}
    "not" { return TOKEN_NOT;}
    "or" { return TOKEN_OR;}
    "return" { return TOKEN_RETURN;}
    "while" { return TOKEN_WHILE;}
    "None" { return TOKEN_NONE;}
    "as" { return TOKEN_AS;}
    "class" { return TOKEN_CLASS;}
    "global" { return TOKEN_GLOBAL;}
    "in" { return TOKEN_IN;}
    "is" { return TOKEN_IS;}
    "nonlocal" { return TOKEN_NONLOCAL;}
    "pass" { return TOKEN_PASS;}

    [_a-zA-Z][_a-zA-Z0-9]* {         
            if(yyleng+10>=buf_size){
                buf_size=yyleng+10;
                buf=make_shared<char[]>(buf_size);
            }
            strcpy(buf.get(), yytext);
            yylval.raw_str=buf.get(); 
            return TOKEN_IDENTIFIER;
        }

    "+"  { return TOKEN_plus;}
    "-"  { return TOKEN_minus;}
    "*"  { return TOKEN_star;}
    "//" { return TOKEN_slash;}
    "%"  { return TOKEN_percent;}
    "<"  { return TOKEN_less;}
    ">"  { return TOKEN_greater;}
    "<=" { return TOKEN_lessequal;}
    ">=" { return TOKEN_greaterequal;}
    "==" { return TOKEN_equalequal;}
    "!=" { return TOKEN_exclaimequal;}
    "="  { return TOKEN_equal;}
    "("  { return TOKEN_l_paren;}
    ")"  { return TOKEN_r_paren;}
    "["  { return TOKEN_l_square;}
    "]"  { return TOKEN_r_square;}
    ","  { return TOKEN_comma;}
    ":"  { return TOKEN_colon;}
    "."  { return TOKEN_period;}
    "->" { return TOKEN_rarrow;}

    [ \t]+ {/* ignore whitespaces */ }
    (#[^\r\n]*)?(\r\n|\r|\n) {/* eat comment & newline */  BEGIN(EndOfLine); return TOKEN_NEWLINE; }
    <<EOF>> {count_indentation("");BEGIN(EndOfProgram);yyleng=1;   return TOKEN_NEWLINE;}
    . {return TOKEN_UNRECOGNIZED;}
}

<EndOfLine>{
    <<EOF>> {count_indentation("");BEGIN(EndOfProgram);}
    (\r\n|\r|\n) {}
    [^\r\n] {yyless(0);BEGIN(INITIAL);}
}

<EndOfProgram>{
    "\n" {
        return TOKEN_NEWLINE;
    }
    <<EOF>> {    
        if(toDedent>0){            
            toDedent--;
            
            return TOKEN_DEDENT;
        }else{
            return 0;
        }
    }    
}
<IndentationEnv>{
    . {
        yyless(0);
        if(IndentationError || toIndent > 0 || toDedent > 0){
            if(IndentationError){
                IndentationError = 0;
                return 0;
            }
            if(toIndent>0){                
                toIndent--;            
                return TOKEN_INDENT;
            }
            while(toDedent>0){              
                toDedent--;                
                return  TOKEN_DEDENT;
            }
        }else{            
            BEGIN(Content);
        }
        
    }
}

%%

void count_indentation(const char *s)
{
    /* 
        called when a non-empty new line is encounterd, or EOF was reached
    */
    int len=strlen(s),count=0,spaces;
    for(int i=0;i<len;++i){
        if(s[i]==' '){
            ++count;
        }else{
            count+=8-(count%8);
        }
    }    
    if(count > stack_indent.top()){
        stack_indent.push(count);
        toIndent++;
    }else{
        while(count<stack_indent.top()){
            stack_indent.pop();
            toDedent++;            
        }
        if(stack_indent.top()<count){
            IndentationError=1;
        }
    }
}


