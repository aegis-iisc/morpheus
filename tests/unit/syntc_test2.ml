open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 


let x = Evar (Var.fromString "x") 
let y = Evar (Var.fromString "y")
let t_val = Eval (ILit 9)
let t_lam = Elam ([x], t_val)
let t_app = Eapp (Evar "t_lam", [y])

let t_match = Ematch (x , 
                        [{constructor= Var.fromString "Cons";
                          args = [Var.fromString "x"; Var.fromString "xs"];
                        exp = t_app}])

let t_ret1  = Eret x

let t_ret2 = Eret (Evar "t_val")

let t_bind = Ebind (Evar "z", t_ret1, t_ret2)



let eps = Eparser (Eps) 

let cparsera = Eparser (Char 'a')
let cparserb = Eparser (Char 'b')


let bot = Eparser (Bot)
let altab = Eparser (Alt (Char 'a', Char 'b'))  

let t_lamb = Elam ([x], cparserb)
let bind = Eparser (Bind (Eparser (Char 'a'), 
                        Evar ("t_lamb")))  

 
let choice (p1, p2) = 
        match (p1, p2) with 
            | (Eparser pr1, Eparser pr2) -> 
                Eparser (Alt (pr1, pr2))
            | (_ , _) -> raise (CompilerExc "Incorrect Term")

let altab = choice (cparsera, cparserb)
 
 let any listP = 
    assert (List.length listP > 0);
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

let (>>=) e1 e2 = Eparser (Bind (e1, e2))  

(*A helper function to easily write do expressions *)
let doExp ls retExp = 
    assert (List.length ls > 0);
    let (bv1, e1) = List.hd ls in 

    let rec do_term doacc remaining = 
        match remaining with 
        | [] -> doacc 
        | x :: xs ->
            let (bvi, ei) = x in 
            do_term (doacc@[(Evar bvi, ei)]) xs  
     in
        
     Edo (
            (do_term [(Evar bv1, e1)] (List.tl ls)), 
            Elet (Evar "ret", retExp, Eret (Evar "ret")))   

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

let startest = star (Var "eps") 

 
let number = (star (Var "digit")) >>= (Elam ([Evar "ys"], 
                                        Eapp (Evar "int_of_string", [Evar "ys"]))) 


 
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
let count n p np = 
        match (n, p) with 
            | (Evar nmame, Var pname) ->     
                let countnp =      
                    Fix (Elam ([Evar np], 
                              Elam ([n], 
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
                                           Elam ([(Evar "fst")], 
                                                      Eparser 
                                                          (Bind (
                                                          (*let count_p_n_minus_1 = count_p (n-1) in 
                                                            count_p_n_minus_1*)
                                                            (*let  nminus1 = subsone n in   *)
                                                              Elet (Evar "nminus1", 
                                                                      (Eapp (Evar "subsone", [n])),
                                                                       Eapp (Evar np, [Evar "nminus1"])
                                                                   ), 

                                                              Elam ([(Evar "snd")], Elet (Evar "returnval", 
                                                                      (Eapp (Evar "cons", [Evar "fst"; Evar "snd"])),
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
                      


let four = Evar "four" 

let counttest = count four (Var "eps") "countnp"

let countndigit =  (count (Evar "n") (Var "digit") "countndigit")

let countfourdigit = Eapp (Evar "countndigit", [four])


let testapp = (Eapp (Evar "subsone", [four]))

let testapp1 =   Eapp (Evar "countndigit", [four])


let testapp2 = Elet ( Evar "nminus1", 
                     (Eapp (Evar "subsone", [four])),
                      Eapp (Evar "countndigit", [Evar "nminus1"]))

let testlet = Elet (Evar "nminus1", 
                    Eapp (Evar "subsone", [four]),
                    Evar "nminus1")

let testlam =  Elam ([(Evar "n")], 
                        (Eapp (Evar "subsone", [Evar "n"])))

let testBind = Elam([(Evar "n")],
              Eparser 
                (Bind (
                    (*let nminus1 = susone (n) in 
                    subsone nminus1) >>= 
                    \snd .
                        let retval = subsone snd in 
                        ret retval
                    *)   
                    Elet ( Evar "nminus1", 
                            (Eapp (Evar "subsone", [Evar "n"])),
                             Elet (Evar "ret1",
                                    Eapp (Evar "subsone" , [Evar "nminus1"]),
                                    Eret (Evar "ret1"))
                                
                         ), 

                    Elam ([(Evar "snd")], Elet (Evar "returnval", 
                            (Eapp (Evar "subsone", [Evar "snd"])),
                                 Eret (Evar "returnval")
                                 )                                                                
                        )
                    )
                )
            )             
                        
(*  
let len = number 
let content = Elam ([Evar "y"], count y (Var "digit"))  
let chunk = Eparser (Bind (len, content))
 *)

(*TODO :: Add a test for libraries 
Add tests for Dref, ref , assign and do
create an easy surface in ml for do block



*)
(* do {l <- len
    con <- content l
    let res = PNG {l;con} in 
    return res} 
 This is also a  test for Type Constructors   
    *)
let do_test = 
    let do_block = [("l", Eparser (Var "number"));
                    ("con", Eapp (Evar "countndigit", [Evar "l"]))] 
    in

    let ret_exp = Eapp (Evar "Pair", [Evar "l"; Evar "con"]) in 
    doExp do_block ret_exp



(* let us write a library of derived combinators and parsers 
For most we need fixpoint combinator*) 

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
            let annotated = Gamma.find gamma "testBind" in    
            R.verifyRParser gamma sigma delta testBind  annotated
        with 
            | e -> 
                raise (e);
                let (gamma, delta, vc, refty) = STC.synthesizeType gamma sigma delta digit  in 
                Printf.printf "%s" (RefinementType.toString refty)
                   
  else 
        raise (CompilerExc ("Required 1 args provided "^(string_of_int num_args)))  
  












