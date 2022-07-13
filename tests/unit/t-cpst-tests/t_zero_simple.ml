module Trans = TypedTransLang
module SB = SigmaBuilder
module TM = TypesMap
module FM = FormMap
open SB  

let specfile = "tests/unit/t-cpst-tests/t_zero_simple.spec"  

(*parse the associated spec file*)
let ast = SB.parseLSpecFile specfile 
let () = Printf.printf "%s" ("\n ########SPECS######### \n "^(SpecLang.RelSpec.toString ast)) 
let (tenv, formenv) =  SB.buildSigma ast  
let getType s = TM.find tenv s  
let getFormula s = FM.find formenv s 
let gamma = SB.initializeGamma ast
(*define placeholder functions in L term with types*)
let res = Trans.trivial_var "res"  
let init = Trans.T_assign( (T_var "res"), (T_cref (T_const (ILit 0))))  
let step1 = Trans.T_lam ("x", (T_var "x"), getType ("step1"))  
let finalqf = Trans.T_dref (T_var  "res") 
let finalother = Trans.trivial_unit
(*define transducer*)     
let t_zero =                    
        let states_st = ["q0";"qf"] in 

       (* let regs = [(res, SpecLang.RefTy.fromTyD (SpecLang.TyD.Ty_int))] in *)
        let regs = [(res, getType "res")] in 
        let d1 = Trans.Del {name = "d1";src = "q0"; tgt = "qf"; guard=getFormula ("guard1"); step=step1; inv = SpecLang.P.True} in 

        let final = Trans.Final {fin = fun (st:Trans.state) -> 
                                match st with 
                                   | "qf" -> (finalqf, getType ("finalqf"))
                                   | _ -> (finalother, getType ("finalother"))} in  
        let transition_system =  Trans.Trans { regs = regs;
                            states=states_st;
                            start = "q0";
                            final = ["qf"];
                            finalizer = final;        
                            (*A term for let cnt = ref 0 , and A type M {true} unit {update h' cnt 0}*)
                            init =  (init ,getType "init");
                            deltas = [(d1, getType ("step1"))];
                            annot = getType ("annot")}
        in    

        Trans.ST transition_system

let () = 
   Morpheus.verifyCPST gamma t_zero (getType "annot")     
