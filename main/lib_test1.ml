
module Lib = Lib
open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 
exception CompilerExc of string

 

let len = Lib.number 
let content = Elam ([Evar "y"],   Elet (Evar "con", 
                                    Lib.count (Evar "y") (Var "digit"),
                                    Pair ())  
let png_chunk = Eparser (Bind (len, content))




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
            let annotated = Gamma.find gamma "len" in    
             let () = Printf.printf "%s" ("\n ********Annotated*********\n  "^(RefinementType.toString annotated)) in 
            R.verifyRParser gamma sigma delta len annotated
        with 
            | e -> 
                raise (e);
                let (gamma, delta, vc, refty) = STC.synthesizeType gamma sigma delta len  in 
                Printf.printf "%s" (RefinementType.toString refty)
                   
  else 
        raise (CompilerExc ("Required 1 args provided "^(string_of_int num_args)))  
  