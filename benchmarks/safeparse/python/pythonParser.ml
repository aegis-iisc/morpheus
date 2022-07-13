open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 




type tree 'a = Tree {term : 'a; 
                    indentT : int; 
                    children : [tree]}


let ist = ref 0
let indent = ref 0

type pterm = string


let indentT t = 
        let Tree{indentT;_} = t in 
        indentT

(*
while_stmt → ’while’> ; test ; ’:’> ; suite
suite → NEWLINE> ; block> | 
        stmt_list ; NEWLINE> 
block → |statement|∗
 *)
t_while = %1 * 0.82 
    do
    wt <- offsideString "while"
    test <- offside t_exp;
    colont <- offsideString ":"
    suite <- suite 
    Tree {node : While test stmts; %3*0.10
          indentT : indent (wt); %1*0.15
          children : (wt :: (test :: suite)) } %3* 0.12

suite = %1 * 0.79
        do 
        nl <- newline 
        stmts <- stmts
        Tree {node = Suite stmts; %1* .30
              indentT = indentT (nl); %1 * .15
              children = stmts}


(*stmt: 'pass' <|> 'break' <|> 'continue' <|> 'global' NAME (',' NAME)* <|> inport*)

stmt = %1 
        string "pass"
        <|> string "break"
        <|> string "continue"
        <|> string "global" many1 name  2*0.82
        

stmts = many stmt 2* 0.79

t_exp = identifier %1  


offside_string s = do %1 * 0.96
            is <- !ist
            i <- indent 
            if (i > is)
                res <- string s 
                Tree {node = String res; 3* 0.15
                      indentT = i;
                      children = []}
             