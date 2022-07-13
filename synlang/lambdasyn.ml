(*defined Var or import from the specLang*)
open Printf 
open SpecLang 
exception IncorrectExp of string     
exception LambdaSynUnimplemented of string 
module RefTy = RefinementType

type var = Var.t 


type caseExp = {constructor : var;
                args : var list ;
                exp : monExp}


(* Extend this to add polymorphic consturcts
First create an example with monomorphic types *)
and value = ILit of int
            | BLit of bool 
            | SLit of string 
            | CLit of char 
            | Loc of var 
            
(* and _ parserPrim = 
        | Eps : unit parserPrim  
        | Bind : 'a parserPrim * ('a -> 'b parserPrim) -> 'b parserPrim   
        | Char : char -> char parserPrim
        | Bot :  'a parserPrim 
        | Alt : 'a parserPrim * 'a parserPrim -> 'a parserPrim 
        | Map : ('a -> 'b) * 'a parserPrim -> 'b parserPrim 
        | Fix : ('a parserPrim -> 'a parserPrim) -> 'a parserPrim 

 *)            
(* 
and _ parserPrim = 
        | Eps : unit parserPrim  
        | Bind : 'a parserPrim * ('a -> 'b parserPrim) -> 'b parserPrim   
        | Char : char -> char parserPrim
        | Bot :  'a parserPrim 
        | Alt : 'a parserPrim * 'a parserPrim -> 'a parserPrim 
        | Map : ('a -> 'b) * 'a parserPrim -> 'b parserPrim 
        | Fix : ('a parserPrim -> 'a parserPrim) -> 'a parserPrim
        | Ret : 'a -> 'a parserPrim  *)

(* the shapes must be enforced using typing rules *)
and parserPrim = 
        | Eps  
        | Bind of monExp * monExp    
        | Char of char 
        | Bot  
        | Alt of parserPrim * parserPrim  
        | Map of monExp * parserPrim (* t1 -> t2 * parserPrim  *) 
        | Fix of monExp (* Must provide the type for the function
                                    Fix (parserPrim -> parserPrim) *) 
        | Var of var  
        | Ret of  monExp  (* return Evar v assuming Normal Form *)
        | Der of parserDerived

and parserDerived = 
        | Any of (parserPrim) list
        | Star of parserPrim 
        | Plus of parserPrim 
        | Count of int * parserPrim 
        | Seq of (parserPrim) list 

(*TODO add typing rules for the ref, dref , let and do*)
and monExp = 
        | Evar of var 
        | Eval of value
        | Elam of (monExp list) * monExp (*Named Lambda Elam x1 : t1, x2:t2 . body *)
        | Eapp of monExp * (monExp list) (*Eapp foo [x1, x2, x3,...xn] *)
        | Ematch of monExp * (caseExp list) 
        | Eret of monExp 
        | Ebind of monExp * monExp * monExp (* Ebind bind e1 e2 == e1 >>= \bind. e2 *)
        | Ecapp of var * ( monExp list ) 
        | Edo of ((monExp * monExp) list * monExp) (*do [x <- E] in retrun e this will be syntactically translated to Ebind *)
        | Eite of (monExp * monExp * monExp)
        | Elet of monExp * monExp * monExp
        | Eskip
        | Eref of var  
        | Eassign of var * monExp  
        | Edref of var
        | Eparser of parserPrim   
    

and typedMonExp = {expMon:monExp; ofType:RefTy.t }


(* lower : monExp -> parserPrim *)
let lower me = 
    match me with 
        | Eparser p -> p 
        | _ -> raise (IncorrectExp "lowering a non-Parser Monadic expression")

type path =  monExp list 


(*The t ~ H relation
The exact logic can be made less or more precise*)
let satHypothesis (t : path) (hypothesis : path) : bool = 
    true


let equalVal v1 v2 = 
    match (v1, v2) with 
        | (ILit i1, ILit i2) ->  i1 == i2
        | (BLit b1, BLit b2)  ->   b1 == b2
        | (SLit s1, SLit s2)  ->   s1 == s2
        | (CLit c1, CLit c2) ->   c1 == c2
        | (Loc v1, Loc v2) ->  Var.equal v1 v2
        | (_, _) -> false
(*monExp instantiate Eq class *)            
let rec equalMonExp m1 m2 =
      match (m1, m2) with
        | (Eval v1, Eval v2) -> equalVal v1 v2
        | (Evar v1, Evar v2) -> Var.equal v1 v2 
        | (Elam (arglist1, body1), Elam (arglist2, body2)) ->
                (try
                    (List.fold_left2 (fun accBool arg1 arg2 -> 
                        accBool && (equalMonExp arg1 arg2)) true arglist1 arglist2) 
                    && (equalMonExp body1 body2) 
                with 
                 Invalid_argument e -> false)

        | (Eapp (fun1, arglist1), Eapp (fun2, arglist2))->
                (try
                    (equalMonExp fun1 fun2) && 
                
                    (List.fold_left2 (fun accBool arg1 arg2 -> 
                        accBool && (equalMonExp arg1 arg2)) true arglist1 arglist2) 
                    
                with 
                 Invalid_argument e -> false)

                 
        | (Ematch (matchingArg1, caselist1),Ematch (matchingArg2, caselist2)) -> 
                (equalMonExp matchingArg1 matchingArg2)  
                         
        | (Edo (l1, ret1), Edo (l2, ret2)) -> 
                raise (LambdaSynUnimplemented "Edo equality case")
        | (Eite (b1, tr1, fl1), Eite (b2, tr2, fl2))-> 
                equalMonExp b1 b2 && equalMonExp tr1 tr2 && equalMonExp fl1 fl2
        | (Eparser _, Eparser _) -> raise (IncorrectExp " Equality checking not decidable")
        |  (_,_) -> false         

and equalTypedMonExp (tme1 : typedMonExp) (tme2 : typedMonExp) = 
    equalMonExp (tme1.expMon) (tme2.expMon)



let val_toString v = 
        match v with 
            ILit i -> string_of_int i 
            | BLit b -> string_of_bool b 
            | SLit s -> s 
            | CLit c -> Char.escaped c 
            | Loc var -> "location "^(Var.toString var)


let rec monExp_toString (m:monExp) = 
    match m with 
        | Eval v -> val_toString v 
        | Evar v -> (v)
        | Eret ret ->  ("return "^(monExp_toString ret))
        | Ebind (mne, mne1, mne2) -> ((monExp_toString mne1)^" \n \t >>= \lambda "^
                                    (monExp_toString mne)^" . \n \t "^
                                    (monExp_toString mne2 ))  
        | Ecapp (cname, argls) -> "Ecapp "^(cname)^" ( "^(
                                List.fold_left (fun accstr ai -> 
                                                accstr^", "^(monExp_toString ai)) "" argls

                                                )^" )" 
        | Ematch (matchingArg, caselist) -> 
                let caselist_toString = 
                    List.fold_left (fun accstr casei -> (accstr^" \n | "^(caseExp_toString casei))) " " caselist 
                in 
                ("Ematch "^(monExp_toString matchingArg)^" with "^caselist_toString)
        | Eapp (fun1, arglsit) -> 
            ("apply "^(monExp_toString fun1)^"  ("^
                (List.fold_left 
                    (fun accStr argi -> accStr^", "^(monExp_toString argi)^" )") ""  arglsit))        
        
        | Edo (l, ret) -> 
                let s = 
                    "do {"^(List.fold_left (fun s (bvi, mei) -> (s^";\n "^((monExp_toString bvi)^" <- "^(monExp_toString mei)))) "" l) in
                let s = s^(monExp_toString ret)^";\n}" in 
                s       
        | Elet (bound, exp1, exp2) -> 
                ("let "^(monExp_toString bound)^" = "^(monExp_toString exp1)^" in \n "^(monExp_toString exp2)) 
        
        | Eskip -> "Eskip"
        | Eite (bi, ttr, tfl) -> 
                ("If ("^(monExp_toString bi)^" ) then \n "^(monExp_toString ttr)^" \n else "^(monExp_toString tfl))
        
        | Eparser p -> 
                    (" ParserPrimitive "^(parserPrim_toString p)) 
        | Elam (args, body) -> 
                    let argsStr = List.fold_left 
                                (fun accstr me_argi -> accstr^(", ")^(monExp_toString me_argi)) "[ " args in 
                    let argsStr = argsStr^" ] -> " in 
                    let bodyStr = monExp_toString body in 
                    ("fun "^argsStr^bodyStr)

        | _ -> "Other expression"  


and parserPrim_toString (p : parserPrim) : string  = 
    match p with 
        | Var v -> ("Var "^v) 
        | Eps -> "eps"
        | Bind (p1, k) -> (monExp_toString p1)^" >>= "^(monExp_toString k)
        | Char c -> ("Character "^(Char.escaped c))
        | Bot -> "bot"
        | Alt (p1, p2) -> (parserPrim_toString p1)^" <|> "^(parserPrim_toString p2)
        | Fix (func) -> "fix ( "^(monExp_toString func)^" )"
        | Ret v -> "ret "^(monExp_toString v)
        | _ -> "Non Interesting Parser"  
(*We will add more auxiliary functions here as we go along synthesis*)
and typedMonExp_toString (t:typedMonExp) : string = 
   let {expMon;ofType} = t in  
   ("{ \n"^(RefTy.toString ofType)^" \n "^monExp_toString expMon^" \n }") 

and caseExp_toString (t : caseExp) : string = 
    let argsToString = List.fold_left (fun accstr argi -> (accstr^" ,"^(Var.toString argi))) " " t.args in 
    ("CASE "^(Var.toString t.constructor)^" ( "^(argsToString)^" ) -> "^(monExp_toString t.exp))

let rec componentNameForMonExp mExp = 
        match mExp with 
         | Evar v -> (v)
         | Eapp (v , _) -> 
                (match v with 
                    | Evar v1 -> v1
                    | _ -> raise (IncorrectExp "a component is either a variable or a fun app"))
         | Ecapp (v, args) -> v
         | Edo (bound, exp) -> componentNameForMonExp exp
         | _ -> raise (IncorrectExp "a component is either a variable or a fun app")
       
        


let getExp (t : typedMonExp) =
    let {expMon;_} = t in expMon

let getType (t : typedMonExp) = 
   let {ofType;_} = t in ofType


let pathToString (p:path) = 
        (List.fold_left (fun accstr ei -> accstr^(" ---> ")^(monExp_toString ei)) "pp-path " p)^"\n"

let previousComponent (p:path) = 
    if (List.length p < 2) then None 
        else 
         Some (List.nth (p) ((List.length p) - 2))

let previousPath (p : path) =
        if (List.length p < 1) then None
        else 
         Some (List.rev (List.tl (List.rev p)))


let merge matchingArg constructors consArgsList caseBodyList = 
       let () = Printf.printf "%s" (string_of_int (List.length constructors) )in 
       assert (List.length constructors == List.length consArgsList);
       assert (List.length consArgsList == List.length caseBodyList);
       
            
       let rec loop c a b cexpList = 
            match (c, a, b) with 
                | ([],[],[]) -> cexpList
                | (x::xs, y::ys, z::zs) -> 
                     let caseExp_i = {constructor =x;args=y;exp=z} in 
                     loop xs ys zs (cexpList@[caseExp_i])     
        in 
        
       let megerdCaseExpList = loop constructors consArgsList caseBodyList [] in 
       
       let mergedExp = Ematch(matchingArg, megerdCaseExpList) in 
       mergedExp




let rec substitute (subs : (monExp * monExp) list) (m:monExp) : monExp = 
      (*TODO : unimplemented*)
      m
    (* match m with 
        | Evar v -> (v)
        | Eret ret ->  ("return "^(monExp_toString ret))
        | Ebind (mne, mne1, mne2) -> ((monExp_toString mne1)^" \n \t >>= \lambda "^
                                    (monExp_toString mne)^" . \n \t "^
                                    (monExp_toString mne2 ))  
        | Ecapp (cname, argls) -> "Ecapp "^(cname)^" ( "^(
                                List.fold_left (fun accstr ai -> 
                                                accstr^", "^(monExp_toString ai)) "" argls

                                                )^" )" 
        | Ematch (matchingArg, caselist) -> 
                let caselist_toString = 
                    List.fold_left (fun accstr casei -> (accstr^" \n | "^(caseExp_toString casei))) " " caselist 
                in 
                ("Ematch "^(typedMonExp_toString matchingArg)^" with "^caselist_toString)
        | Eapp (fun1, arglsit) -> 
            ("apply "^(monExp_toString fun1)^"  ("^
                (List.fold_left 
                    (fun accStr argi -> accStr^", "^(monExp_toString argi)^" )") ""  arglsit))        
        
        | Edo (bound, exp) -> 
                ("do "^(monExp_toString bound)^" <- "^(monExp_toString exp)) 
        | Eskip -> "Eskip"
        | Ehole t -> ("[?? : "^(RefTy.toString t^"]"))
        | _ -> "Other expression"  
 *)




