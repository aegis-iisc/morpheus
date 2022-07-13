open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 



let eps = Eparser (Eps) 
let cparser c = Eparser (Char c)
let bot = Eparser (Bot)

let (<|>) p1 p2 = 
        match (p1, p2) with 
            | (Eparser pr1, Eparser pr2) -> 
                Eparser (Alt (pr1, pr2))
            | (_ , _) -> raise (CompilerExc "Incorrect Term")

let (>>=) e1 e2 = Eparser (Bind (e1, e2))  
let ( *> ) e1 p1 = Eparser (Bind (e1, Elam (Evar "_i", p1)))
let ( <* ) p1 e2 = Eparser (Bind (e1, Elam (Evar "_i", EBind (p1, Eret "_i"))))



let assign v e2 eb = e2 >>= (Elam (Evar v, eb))  

let apply funNam args = Eapp (Evar funName, List.map (fun aiName -> Evar aiName) args)

let dostmt ls = 
    let fst = List.hd ls in 
    
    let rec term altacc remaining = 
        match remaining with 
        | [] -> raise (CompilerExc "No Return Statement") 
        | x :: xs -> 
           match x with 
            | Elet (_, _,_) -> altacc x 
            | Eret _ -> altacc x 
            | _ -> term (altacc x) xs
     in
    
    Eparser (term fst (List.tl listP))       



let indented p = 
                (notEndBlock *> p) <* keepTerminator

 
let any listP = 
    let fst = List.hd listP in 
    
    let rec term altacc remaining = 
        match remaining with 
        | [] -> altacc 
        | x :: xs -> 
           term (Alt (altacc, x)) xs
     in
    
    Eparser (term fst (List.tl listP))       


let digit = any [Char '0'; Char '1'; Char '2';Char '3';
                Char '4'; Char '5'; Char '6'; Char '7';Char '8';
                Char '9']




let onetwothree = any [Char '1'; Char '2';Char '3']


(*star : 'a parserPrim -> 'a list parserPrim  *)
(*star  = \p. fix (\p_star. map (\_ -> []) `choice' 
                p >>= \x. 
                p_star >>= \xs . (x :: xs) ) 

think of bind and Var, 

once we have done that, we can define star
        *)
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



let number = (star (Var "digit")) >>= (Elam ([Evar "ys"], 
                                        Eapp (Evar "int_of_string", [Evar "ys"]))) 



let identifier = many1 letter


let keyword s = 
        do 
        i <- identifier
        if ( i = s) then i 
        else fail 

let string s = keyword s

let reserved s = keyword s



(* count (n : var) (p : parserPrim)  *)
let count n p = 
        
        match (n, p) with 
            | (Evar nmame, Var pname) ->     
                let countnp =      
                Fix (Elam ([Evar "countnp"], 
                            Eite 
                               (*condition *) (
                                Eapp (Evar "ltz", [n]),
                                (*true branch *)
                                Eparser (Bind (Eparser Eps, 
                                        Elam ([], Eret (Evar "nil")))),
                                (*false branch*)    
                                Eparser (
                                    Bind (
                                      Eparser (Var pname), 
                                         Elam ([(Evar "x")], 
                                                    Eparser 
                                                        (Bind (
                                                        (*let count_p_n_minus_1 = count_p (n-1) in 
                                                          count_p_n_minus_1*)
                                                        
                                                                (*let  nminus1 = subsone n in   *)
                                                            Elet ( Evar "nminus1", 
                                                                    (Eapp (Evar "subsone", [n])),
                                                                    Eapp (Evar "countnp", [Evar "nminus1"])
                                                                 ), 
                                                            
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
                  in Eparser countnp    
                                
            | (_, _) -> raise (CompilerExc "the count takes twp variables bound to a var and a parser")               
