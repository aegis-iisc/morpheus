
open SpecLang
module Syn = Lambdasyn
module STC = Syntypechecker
module VCE = Vcencode 
module VC= VerificationC 
module Gamma = Environment.TypingEnv 



exception CantDischargeVC



let discharge_VCS (vcs : VC.standardt list)  = 
(*discharge VCs*)
let  dischargeVC i vc =
        let () = Printf.printf "%s" ("\n ***************** VC number "^(string_of_int i)^"\n \n "^(VC.string_for_vc_stt vc)^"***************************") in 
        match (VCE.discharge vc) with   
        VCE.Success -> 
            Printf.printf  "%s" ("VC# "^(string_of_int (i+1))^" discharged\n")
        | VCE.Undef -> (Printf.printf "%s" ("Solver timeout  while trying to \
                  \discharge VC #"^(string_of_int (i+1))); 
                   (* z3_log_close (); *)
          raise CantDischargeVC)
        |VCE.Failure -> (Printf.printf "%s" ("VC # " ^(string_of_int i)^
                                             " is invalid!"); ();
                                           raise CantDischargeVC)
in    
let unit_lists = List.mapi dischargeVC vcs in   
Printf.printf "%s" "The implementation is correct w.r.t given specification!\n"


(* Gamma; SIgma; Delta |- exp : t*)
let verifyRParser gamma sigma delta (exp :  Syn.monExp) (t : RefTy.t) = 
    let () = Printf.printf "%s" ("\n  Morpheus Exp :: "^(Syn.monExp_toString exp)) in 
    let () = Printf.printf "%s" ("\n AnnotatedType :: "^(RefTy.toString t)) in 
    
    let (gamma, delta, vcs, refty) = STC.checkType gamma sigma delta exp t in 
    let () = Printf.printf "%s" ("\n Number-VCS "^ (string_of_int (List.length vcs))) in 
    let standard_vcs = List.map (fun (vc) -> (VC.standardize vc)) vcs in    
    let () = Printf.printf "%s" "\n Final VCs" in 
  (*   let () = Printf.printf "%s" "\n Final Non STANDART" in 
    
    let () = List.iter (fun vc -> Printf.printf "%s" ("\n"^(VC.string_for_vc_t vc))) vcs in      
  *)
    let () = Printf.printf "%s" "\n Final STANDART" in 
    
    let () = List.iter (fun vc -> Printf.printf "%s" ("\n"^(VC.string_for_vc_stt vc))) standard_vcs in      
    discharge_VCS standard_vcs
    