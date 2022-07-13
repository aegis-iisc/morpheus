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
let t_bind = Ebind (Evar "z", t_ret1, t_val)
(*
let goal = Ecapp (Var.fromString "Cons", [x, Evar.fromString "xs"])

 *)

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
        let annotated = 
            try
                Gamma.find gamma "t_bind" 
            with 
            | e -> raise (STC.TypeSynthExc "No annotation provided")   
        in    
        R.verifyRParser gamma sigma delta t_bind annotated   
  else 
        raise (CompilerExc ("Required 1 args provided "^(string_of_int num_args)))  
  












