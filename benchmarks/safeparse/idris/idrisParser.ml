(*    simple pure 0.10 -0.15 
      simple eff checks 0.35 -0.56
   complex checks 0.70- 0.98 sec
   many 2 vcs
   application 1 per argumeny 
   lambda 1
   constructor app 1 per argument

    *)


exception Fail of string 

open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 


let operator = ["mplus"]

let ist = ref 0

type  tree = Tree of {term : pterm; 
                     indentT : int; 
                     children : tree list}

type exp = string
type pterm = PDoBlock [PDo]
type pdo = DoExp of exp | DoLet of (exp * exp) 

let indentT t = 
        let Tree{indentT;_} = t in 
        indentT

let term t = 
        let Tree{term;_} = t in 
        term

let children t = 
        let Tree{children;_} = t in 
        children

let identifier = let i = indent in 
                 let x = many letter in 
                     Tree {term = String.of_seq x; 
                          indentT = i;
                          children = []}

     
let do_  = 
        do lt <- 
            reserved "let"  
            i <- name
            reservedOp "=" 
            e <- expr 
            let term = DoLet i e in 
            Tree {term = term; 
                 indentT= indentT (lt);
                 children =[lt;i;e]}
   <|>  do 
           e <- expr 
           let term = DoExp e in  
           Tree {term; 
                    indentT (udk);[ude;e]}
                       
   <|> do 
          e <- expr 
          let term = DoExp e in 
          Tree {term=term;
                indentT = indentT (e);
                [e]} 

let indent =
        do 
          if (lookAheadMatches (operator)) then
            do
               operator
               return (sourceColumn !inp)
          else
               return (sourceColumn !inp


let indentedDo =   %1 * 0.76
        do  ist <- !ist
            i <- indent
            if (i < ist )
               then raise (Fail "end of block")
            else 
                do_ 


let indentedDoBlock () = 
        let last = !ist in 
        let is = last in 
        let lvl' = indentation () in 
        if (lvl' > is) then 
            (ist := lvl'; 
            let res = many (indentedDo) in 
            ist := last;
            res )
        else 
            raise (Fail "Indentation error")




let doBlock 
    =  let dot = indented_reserved "do" in
       let ds = indentedDoBlock () in  
         Tree {term = dot; 
               indentT = indentT (dot);
               children = List.concat [[dot];ds]}



