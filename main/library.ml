open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 



(*star : 'a parserPrim -> 'a list parserPrim  *)
(*star  = \p. fix (\p_star. map (\_ -> []) `choice' 
                p >>= \x. 
                p_star >>= \xs . (x :: xs) ) 
        *)
let star = Elam ([Evar "p"],
                    Fix (Elam ([Evar "pstar"], 
                        Eparser (
                            Alt (
                                Bind (Eparser Eps, 
                                    Elam ([], Eret (Evar "nil"))),
                                (* we need a binding for defining the recursion *)    
                                (
                                    Bind (
                                      Eparser (Var "p"), 
                                         Elam ([(Evar "x")], 
                                                    Bind (
                                                        Eparser (Var "pstar"), 
                                                            Elam ([Evar "xs"], 
                                                                Eret (Eapp (Evar "cons", [Evar "x"; Evar "xs"])))
                                                        )
                                                )
                                    )                             
                                )
                            ) 
                        )
                    )
                )           


(* MLtype : count : int -> 'a parser -> ['a] parser*)
(* Higher-level definition of count
    count = \p. fix (\count_p. \n. 
                            if n <= 0 then 
                                map (\_ -> []))
                            else 
                                p >>= \x.
                                count_p (n-1) >>= xs.
                                (x::xs)     

count : (p : M Q1 v:t Q2) -> n : int -> M {??} v : [t] {}     
 *)
let nminus1 = Eapp (Evar "minus1", [Evar "n"]) 

(* count (n : var) (p : parserPrim)  
count n p  = \p. fix (\p_star. 
                  if (n = 0) then 
                    eps >>= \_. []  
                    map (\_ -> []) `choice' 
                  else 
                    p >>= 
                    \x.    
                    count n-1 p >>= \xs. 
                     (x :: xs) ) 

*)
let count n p = 
        match (n, p) with 
            | (Evar nmame, Var pname) ->     
                let countnp =      
                    Fix (Elam ([Evar "countnp"], 
                              Elam ([(Evar "n")], 
                                (Eite 
                                 (*condition *) (
                                  Eapp (Evar "eqz", [n]),
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

                                                              Elam ([(Evar "xs")], Elet (Evar "returnval", 
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
                            
                    ))
                in 
                Eparser countnp    
                                
            | _ -> raise (CompilerExc "the count takes twp variables bound to a var and a parser")    
 


let choice (p1, p2) = 
        match (p1, p2) with 
            | (Eparser pr1, Eparser pr2) -> 
                Eparser (Alt (pr1, pr2))
            | (_ , _) -> raise (CompilerExc "Incorrect Term")

(* parserPrim list -> monExp  *)
let any listP = 
    let fst = List.hd listP in 
    let rec term altacc remaining = 
    match remaining with 
        | [] -> altacc 
        | x :: xs -> 
           term (Alt (altacc, x)) xs
   in
    term fst (List.tl)       


let doExp ls retExp = 
    assert (List.length ls > 0);
    let (bv1, exp1) = List.hd ls in 

    let rec do_term doacc remaining = 
        match remaining with 
        | [] -> doacc 
        | x :: xs ->
            let (bvi, ei) = x in 
            do_term (doacc@[(Evar bvi, ei)]) xs  
     in
        
     Edo (
            (do_term fst (List.tl ls), 
            retExp)   




(* cparserb : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap). 
            (v = Inlchar (x1) => ([x1 = '1'] \/ [x1 = '2'] \/ [x1 = '3'] \/ [x1 = '4'])
                         /\ includes (h', h, inp) = true) 
                         /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};
*)
let digit = any [Char '0'; Char '1'; Char '2';Char '3';
                Char '4'; Char '5'; Char '6'; Char '7';Char '8';
                Char '9']
        

let number = Bind ( Eapp (Evar "star", [Evar "digit"]), 
                    Elam ([Evar "xs"], 
                            Eapp (Evar "int_of_string", [Evar "xs"])) 



let identifier = Bind ( Eapp (Evar "star", [Evar "alphanum"]), 
                        Elam ([Evar "xs"], 
                            Eret (Evar "xs"))  

(*
State
 {\(h : heap). true} 
 v : {v : int| true}
 {\(h : heap), (v : int), (h' : heap). 
    ilssel(h, inp) = l /\  hd (l) == v1 /\ 
        ([v1 = '0'] \/ [v1 = '1'] \/ [v1 = '2'] \/ [v1 = '3']) };
*)
let pnglen = number



(*x : { v : int | true} ->  
    State  {\(h:heap). true} 
        v : { v :  [char] | true}  
        {\(h : heap), (v: [char]), (h' : heap). (len (v) == fst (v))};
*)        
let content = Elam (Evar "x", 
                    Eapp (Evar "count", [Evar "alpha"; Evar "x"]]))


(*What type must be given to this *)
let chunk = Bind (Eparser pnglen, 
                        content)




let () = 
    let num_args = (Array.length Sys.argv) - 1 in 
    if num_args = 1 then  
        let spec_file = Sys.argv.(1) in 
        let _ = Printf.printf "%s" ("\n specfile :: "^spec_file) in 
        let ast = SEL.parseLSpecFile spec_file in 
        let string_ast = RelSpec.toString ast in 
        let () = Printf.printf "%s" string_ast in 
        let (gamma, sigma) = SEL.elaborateEnvs ast in 
        let delta = P.True in 
      
        (*call  the typecheker/synthesis *)
        try        
            let annotated = Gamma.find gamma "bind" in    
            R.verifyRParser gamma sigma delta alt annotated
        with 
            | e -> let (vc, refty) = STC.synthesizeType gamma sigma delta bind  in 
             Printf.printf "%s" (RefinementType.toString refty)
                   
  else 
        raise (CompilerExc ("Required 1 args provided "^(string_of_int num_args)))  
  












