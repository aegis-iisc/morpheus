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



let ist = ref 0
let indent = ref 0

type pterm = string

type  tree = Tree of {term : pterm; 
                     indentT : int; 
                     children : tree list}

let indentT t = 
        let Tree{indentT;_} = t in 
        indentT



let name () = %1 * 0.67
                let i = indentation () in 
                let x = many letter in 2* 0.13 
                     Tree {term = "name"; %3 * 0.12
                            indentT = i;
                            children = []}

let reserved s = %1
            let i = indentation () in 
            Tree {term = s; %3 * 0.10
                 indentT = i; 
                    children = []}

let expr () = name  () 

(* let indented_reserved s = 
        let ist = get () in 
        let i =  indentation () in 
        if (i < ist )
                then raise (Fail "incorrect indentation")
        else 
             let res = reserved s in 
             res *)

let indented_reserved s = %1 * 0.87
        do ist <- get
           i <- indent
           if (i < ist )
                then fail ("incorrect indentation")
           else 
             resrved s in 
             
(* let extension ()  = reserved "mplus"  *)

let extension   = reserved "mplus" 

(* 
let do_1 = 
        let lt  = reserved "let" in 
        let i = name () in 
        let et = reserved "=" in 
        let e  = expr  () in 
        (* let term = DoLet i e in  *)
        let term = "let" in 
               Tree {term = term; 
                        indentT = indentT lt;
                        children = [lt;i;e]}

let do_2 = 
         let udk = extension () in 
         let e = expr () in  
           (* let term = DoExp e in   *)
           let term = "ext" in 
           Tree {term=term ;
                indentT = indentT (udk);
                children = [udk;e]}
        
let do_3 = 
        let e = expr () in 
          (* let term = DoExp e in  *)
          let term = "exp" in 
          Tree {term=term ;
                indentT = indentT (e);
                children = [e]}
         *)
let do_  = %1 * 0.89
        do lt <- 
            reserved "let"  
            i <- name
            reservedOp "=" 
            e <- expr 
            let term = DoLet i e in %2 * 0.10  
            Tree {term = term;  %3 * 0.10
                 indentT= indentT (lt);
                 children =[lt;i;e]}
   <|>  do udk <- extension 
           e <- expr 
           let term = DoExp e in  %1 * 0.10
           Tree {term; %3 * .10
                    indentT (udk);[ude;e]}
                       
   <|> do e <- expr 
          let term = DoExp e in %1 * 0.10
          Tree {term=term;%3 * 0.10
                indentT = indentT (e);
                [e]} 


(* 

let indentedDo () =   
          let is = get () in 
          let i = indentation () in 
          if (i < is )
                then raise (Fail "end of block")
          else 
            do_ ()  *)

let indentedDo =   %1 * 0.76
        do  ist <- get
            i <- indent
            if (i < ist )
               then raise (Fail "end of block")
            else 
                do_ 


let indentedDoBlock () = %1 * 0.79
        let last = get () in 
        let is = last in 
        let lvl' = indentation () in 
        if (lvl' > is) then 
            (ist := lvl'; 
            let res = many (indentedDo) in %2 * 0.56
            ist := last;
            res )
        else 
            raise (Fail "Indentation error")




1 check 0.86
3 check for Tree .45
1 check concat .15
1 check indentT  .15

let doBlock %1 = 0.86
    =  let dot = indented_reserved "do" in
       let ds = indentedDoBlock () in  
         Tree {term = "doblock"; 
               indentT = indentT (dot);
               children = List.concat [[dot];ds]}




(* 
val do_ : tree pterm
let do_ 
     = (do lt <- 
                reserved "let"
               i <- name
               reservedOp "="
               e <- expr 
               let term = DoLet i e in 
               Tree {term;indentT (lt);[lt;i;e]}
   <|>  do ude <- extension 
           e <- expr 
           let term = DoExp e in  
           Tree {term;indentT (udk);[ude;e]}
                       
   <|> do e <- expr 
          let term = DoExp e in 
          Tree {term;indentT (e);[e]}



let extension = "mplus" 
*)

 