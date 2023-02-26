open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 

(*some simple morpheus expressions and parsers *)
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

 


let four = Evar "four" 



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
  












