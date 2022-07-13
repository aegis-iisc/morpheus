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

let eps = Eparser (Eps) 
let cparser c = Eparser (Char c)
let bot = Eparser (Bot)

let (<|>) p1 p2 = 
        match (p1, p2) with 
            | (Eparser pr1, Eparser pr2) -> 
                Eparser (Alt (pr1, pr2))
            | (_ , _) -> raise (CompilerExc "Incorrect Term")

let (>>=) e1 e2 = Eparser (Bind (e1, e2))  


let star p = 
            match p with 
            | Var pname ->     
                let starparser =  
                    Fix (Elam ([Evar "pstar"], 
                         Eparser (
                            Alt (
                                Bind (Eparser Eps, 
                                    Elam ([], Eret (Evar "nil"))),
                                (* we need a binding for defining the recursion *)    
                                    
                                Bind (
                                      Eparser (Var pname), 
                                         Elam ([(Evar "x")], 
                                                    Eparser (Bind (
                                                        Eparser (Var "pstar"), 
                                                            Elam ([Evar "xs"], 
                                                                Elet (Evar "returnval", 
                                                                    (Eapp (Evar "cons", [Evar "x"; Evar "xs"])),
                                                                    Eret (Evar "returnval")
                                                                    )
                                                            )        
                                                        )
                                                    )    
                                            )
                                    )                             
                                )
                            ) 
                        )
                    )
                 in 
                Eparser starparser
            | _ -> raise (CompilerExc "the star takes a variable bound to a parser")               




let many p = [p ()]

let (<|>) p1 p2 = p1 

let letter () =  'a'

let get () = !ist
let indentation ()  = !indent


let name () = 
                let i = indentation () in 
                let x = many letter in 
                     Tree {term = "name";
                            indentT = i;
                            children = []}

let reserved s = 
            let i = indentation () in 
            Tree {term = s;
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

let indented_reserved s = 
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
   <|>  do udk <- extension 
           e <- expr 
           let term = DoExp e in  
           Tree {term;
                    indentT (udk);[ude;e]}
                       
   <|> do e <- expr 
          let term = DoExp e in 
          Tree {term=term;
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

let indentedDo =   
        do  ist <- get
            i <- indent
            if (i < ist )
               then raise (Fail "end of block")
            else 
                do_ 


let indentedDoBlock () = 
        let last = get () in 
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


  

data IState = {
     ist : Int
     ...
}

getIst = ist (get) 
indent = P.unPos . P.sourceColumn <$> P.getSourcePos
pustIst i = put ( { ist = i })

doBlock :: IdrisParser PTerm
doBlock 
    = do reserved "do"
         ds <- indentedBlock (do_ syn)
         return (PDoBlock ds)
      
do_ :: IdrisParser PDo 
do_     = (do reserved "let"
               i <- name
               ty <- option Placeholder (do lchar ':'
                                            expr' syn)
               reservedOp "="
               e <- expr 
               return (DoLet fc i ty e))
   <|> (do reserved "let"
               i <- expr' syn
               reservedOp "="
               sc <- expr 
               return (DoLetP fc i sc))
   <|> (do i <- name
               symbol "<-"
               e <- expr ;
               return (DoBind fc i e))
   <|> do e <- expr 
          return (DoExp fc e)


indentedDo :: IdrisParser PDO
indentedDo =    ist <- getIst
                do i <- indent
                   if (i < ist )
                    then fail ("end of block")
                    else do_    



indentedDoBlock :: IdrisParser [PDo]
indentedDoBlock  = do 
                   last <- getIst 
                   ist <- last
                   lvl' <- indent
                    if (lvl' > ist)
                        then 
                        putIst lvl'
                        res <- many (indentedDo)
                        putIst last
                        return res 

                    else fail "Indentation error"
                    
