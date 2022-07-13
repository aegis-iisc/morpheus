module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredTerms 
module DPred = Knowledge.DiffPredicate
module DMap = Knowledge.DistinguisherMap
module RelPredicate = Predicate.RelPredicate 
module BasePredicate = Predicate.BasePredicate
(* module PTypeMap = Knowledge.PathTypeMap *)


module VCE = Vcencode 
module P = Predicate  
module RP = Predicate.RelPredicate
module BP = Predicate.BasePredicate
exception SynthesisException of string 
exception Unhandled

exception TypeSynthExc of string 
open Syn







(*TODO : 1. This needs to be generalized for different alfgebraic constructors 
        2. Currently mannualy generating nil and cons preds, this has to be populated 
        by parsing relations from the programmer*)       
let generateNilConstraints (macthedArg) = 
      (*len (ls) = 0*)
      let nil_length = 
        P.Rel(RP.NEq 
              ( RelLang.R (RelLang.instOfRel (RelId.fromString "len"), macthedArg),
                RelLang.relexpr_for_int 0
              )
              )  
      in 
      let () = Printf.printf "%s" ("Nil Length "^(Predicate.toString nil_length)) in 
      nil_length  




let generateConsConstraints (macthedArg : Var.t) (arg_x: Var.t) (arg_xs : Var.t) = 
    let cons_length =  P.Rel
      (RP.NEq( 
        R( (RelLang.instOfRel (RelId.fromString "len")), macthedArg),
                        
       ADD(
          R ( RelLang.instOfRel (RelId.fromString "len"), 
                arg_xs
              ),
          RelLang.relexpr_for_int 1))
        )  in 
     let cons_length_grt_0 = 
      P.Rel(RP.Grt 
              ( R (RelLang.instOfRel (RelId.fromString "len"), macthedArg),
                RelLang.relexpr_for_int 0
              )
              )
      in 
      let cons_length = Predicate.Conj (cons_length, cons_length_grt_0) in 
  let () = Printf.printf "%s" ("Cons Length "^(Predicate.toString cons_length)) in 
      
    cons_length


(*{v : tau | pred} {v : resultchar | v = Inl x /\ pred x
takes a monomrphic relation name , e.g. inlchar, inlbool, etc*)
  let exc_success_predicate (result : (Var.t * TyD.t)) 
                            (inlMono : string) 
                            (success_conseq : Predicate.t) : ( Var.t *  Predicate.t) = 
        let (result_var, result_ty) = result in 
        let x_ident = Var.get_fresh_var "x" in 
        
        (*get an expression Inl x_ident *)        
        let _Inl_x_expr = 
          RelLang.relationInstantiationExp (RelId.fromString (inlMono)) (Var.toString x_ident) in 
        let _v_eq_inl_x = Predicate.Rel (RelPredicate.Eq 
                                (RelLang.V (RelLang.Var(Ident.create (Var.toString result_var)))
                                                , _Inl_x_expr)) in  
        let success_conseq_red = Predicate.applySubst (x_ident, result_var) success_conseq in 
        let exc_predicate = Predicate.If (_v_eq_inl_x, success_conseq_red) in 
        (x_ident, exc_predicate)

  (* {v : tau | v = Inr err /\ pred x *)
  let exc_failure_predicate (err : (Var.t * string)) (inrMono : string) (pred : Predicate.t) : 
            Predicate.t = 
        let (result_var, errmsg ) = err in 
        
        (*get an expression Inr err*)        
        let inr_err = RelLang.relationInstantiationExp (RelId.fromString (inrMono)) errmsg in 
        let v_eq_inr_err = Predicate.Rel (RelPredicate.Eq (RelLang.V (RelLang.Var(Ident.create (Var.toString result_var)))
                                                , inr_err)) in  
        let exc_predicate = Predicate.Conj (v_eq_inr_err, pred) in 
        exc_predicate




(*Takes two refinement types and returns a unified type*)
let  rec unifyWithDisj refTy1  refTy2  =
   let () = Printf.printf "%s" "\n*******Performing Unification with Disjunction *********\n" in 
   let () = Printf.printf "%s" ("\n \n ty of fst  "^RefTy.toString refTy1) in      
   let () = Printf.printf "%s" ("\n \n ty of snd "^RefTy.toString refTy2) in      
           
  let open RefTy in 
     match (refTy1, refTy2) with
         (Base (_, TyD.Ty_unknown, _),_) -> refTy2
       | (_,Base (_, TyD.Ty_unknown, _)) -> refTy1
       (*Disjunction of Predicates*)
       |(Base (bv1,td1,pred1),Base (bv2,td2,pred2)) ->

           let () = Printf.printf "%s" "\n*******unifyWithDisj Base , Base *********\n" in 
           let _ = assert (TyD.sametype td1 td2) in 
           let unified_type = 
                let pred1' = Predicate.applySubst (bv2,bv1) pred1 in
                Base (bv2,td2,Predicate.dot (pred1',pred2))
            in 
            unified_type   
       
       | (MArrow (e1, p1, (v1, t1), p1'), (MArrow (e2, p2, (v2, t2), p2'))) -> 
             let () = Printf.printf "%s" "\n*******Performing M1 : M2 unification with Disjunction *********\n" in 
            assert (Effect.equall e1 e2);
            assert (TyD.sametype (RefTy.toTyD t1) (RefTy.toTyD t2));
            (* 
            FIXME :: Not sure about the joint pre-condition 
            \Gamma |- {\forall h1. p1} v1 : t {\forall h1 v1 h1'. p1'}
            \Gamma |- {\forall h2 . p2} v2 : t {\forall h2 v2 h2' p2'}
            \Gamma |- {\forall h2. p1[h2/h1] /\ p2} v2 : t {\forall h2 v2 h2'. p1'[v2/v1; h2/h1; h2'/h1'] \/  p2'} *)
             let Predicate.Forall (tyds2, p2_free) = p2 in  
             let Predicate.Forall (tyds1, p1_free) = p1 in 
             
             let subst = List.map2 (fun (v2i, _) (v1i, _) -> (v2i, v1i)) tyds2 tyds1 in 
             let p1_substituted = Predicate.reduceMany subst p1 in 



             let Predicate.Forall (tyds2', p2'_free) = p2' in  
             let Predicate.Forall (tyds1', p1'_free) = p1' in 
             

             let subst' = List.map2 (fun (v2i, _) (v1i, _) -> (v2i, v1i)) tyds2' tyds1' in 
             let p1'_substituted = Predicate.reduceMany subst' p1' in 

         
             let pre = Predicate.Forall (tyds2, Predicate.Conj (p2_free, p1_substituted)) in 
             let post = Predicate.Forall (tyds2', Predicate.Disj (p2'_free, p1'_substituted)) in 
             MArrow (e2, pre, (v2, t2), post)
               


       | (Arrow _,Arrow _) -> raise (TypeSynthExc "Unimpl : Case returning arrow")
       
       | _ -> raise (TypeSynthExc "Case rules types not unifiable")       




(* Customized Rules for Parser Combinator Primitives *)
let synthesizeCombAlt gamma sigma delta type_p1 type_p2 : 

        (Gamma.t * 
         Predicate.t * 
         VerificationC.t list *  
          RefTy.t) = 
  (*Γ ⊢ T 1 : M1 {φ1} t1{φ1 ′ }
      * Γ ⊢ T 2 : M2 {φ2} t2 {φ2 ′ }
      * M = M1 ∪ M2 ∪ Nondet
      * M {φ1 ∗ }t1{φ1 ′∗ } = M1.li f t M (T 1)
      * M {φ2 ∗ }t2{φ2 ′∗ } = M2.li f t M (T 2)
      * t = Σ t1 t2
      *----------------------------------------------
       Γ ⊢ T 1<|>T 2 : M {(φ1 ∗ /\ φ2 ∗ )} t {(φ1 ′∗ \/ (φ2 ′∗ )}
      *
      * *)
     let () = Printf.printf "%s" ("\n Synthesizing Type for Combinator Alt \n") in 
     let () = Printf.printf "%s" ("\n First Type "^(RefTy.toString type_p1)) in 

     let () = Printf.printf "%s" ("\n Second Type "^(RefTy.toString type_p2)) in 
     
     let m1 = RefTy.get_effect type_p1 in 
     let m2 = RefTy.get_effect type_p2 in 
     let () = Printf.printf "%s" ("\n Calculating lub  \n") in 
     let lubM = (*M*)RefTy.lub_effects type_p1 type_p2 in
        

     (* TODO :: Implement the lifting functions to lift the local effect types to combined effect*)   
     (* let lifted_ty1 = RefTy.liftM type_p1 lubM in 
     let lifted_ty2 = RefTy.liftM type_p2 lubM in 
      *)

     let lifted_ty1 = type_p1 in 
     let lifted_ty2 = type_p2  in  
     (*what if the lifted is arrow*)      
     let RefTy.MArrow (lubM, phi1_star, (v1, t1), phi1'_star) = lifted_ty1 in 
    (* let RefTy.MArrow (e_lub, phi2_star, t2, phi2'_star) = lifted_ty2 in *)
     
     let RefTy.MArrow (lubM, phi2_star, (v2, t2), phi2'_star) = lifted_ty2 in 
     let unified_t = TyD.unify (RefTy.toTyD t1) (RefTy.toTyD t2) in 
    
    (*create alt pre*)
     let fresh_h = Var.get_fresh_var "h" in 
     let fresh_v = Var.get_fresh_var "v" in 
     let fresh_h' = Var.get_fresh_var "h'" in 
       
      (*\forall h x h' \phi -> forall h x h_int 
        *
        * We assume that all the bound variable have the same naming structure h x h_int etc 
        * TODO :: Create a general substitution of bounded variables so that we can substitute one or more or all of the bound variables*)
     let pre_1 = VC.apply phi1_star [(fresh_h, TyD.Ty_heap)] in 
     let pre_2 = VC.apply phi2_star [(fresh_h, TyD.Ty_heap)] in 
     let p_1_conj_2 = P.Conj (pre_1, pre_2) in 
     let var_binds_pre = [(fresh_h, TyD.Ty_heap)] in    
     let pre_phi = P.Forall (var_binds_pre, p_1_conj_2) in 
       
     
     let post_1 = VC.apply phi1'_star [(fresh_h, TyD.Ty_heap);(fresh_v, unified_t);(fresh_h', TyD.Ty_heap)] in 
     
     let post_2 = VC.apply phi2'_star [(fresh_h, TyD.Ty_heap);(fresh_v, unified_t);(fresh_h', TyD.Ty_heap)] in 
     
     let post_disj = P.Disj (post_1, post_2) in
     let var_binds_post = [(fresh_h, TyD.Ty_heap);
                              (fresh_v, unified_t);
                              (fresh_h', TyD.Ty_heap)] in 
     let post_phi = P.Forall (var_binds_post, post_disj) in 
     let alt_type = RefTy.MArrow (lubM, pre_phi, (fresh_v, (RefTy.fromTyD unified_t)), post_phi)in 
     let () = Printf.printf "%s" ("\n Type Synthesized for Alt "^(RefTy.toString alt_type)) in
     (gamma, delta, [], alt_type) 
             


let rec synthesizeCombBind gamma sigma delta type_p1 type_k : 
        (Gamma.t * 
         Predicate.t * 
          VerificationC.t list * 
          RefTy.t) = 
     let RefTy.MArrow (e1, phi1, (v1, t1), phi1') = type_p1 in 
      match type_k with 
      | RefTy.Arrow ((x, t_x), type_p2) -> 
          let RefTy.MArrow (e2, phi2, (v2, t2), phi2') = type_p2  in 
          let lubM = (*M*)RefTy.lub_effects type_p1 type_p2 in
   
           
          let fresh_h = Var.get_fresh_var "h" in 
          let fresh_h_int = Var.get_fresh_var "h_int" in 
          (* Add the h_int and x as existenitials in env *)
          let gamma = VC.extend_gamma (fresh_h_int, RefTy.lift_base (TyD.Ty_heap)) gamma in 
          let gamma = VC.extend_gamma (x, t_x) gamma  in 

          (** TODO : lifting is not yet defined *)
          (* let lifted_ty1 = RefTy.liftM type_p1 lubM in 
          let lifted_ty2 = RefTy.liftM type_p2 lubM in 
           *)
          let lifted_ty1 = type_p1 in 
          let lifted_ty2 = type_p2 in 


          (*what if the lifted is arrow*)      
          let RefTy.MArrow (lubM, phi1_star,(v1, t2) , phi1'_star) = lifted_ty1 in 
          let RefTy.MArrow (lubM, phi2_star,(v2, t2), phi2'_star) = lifted_ty2 in       
                
           
          (* create bind pre *)
          let pre_1 = VC.apply phi1_star [(fresh_h, TyD.Ty_heap)] in  
          let pre_2 = VC.apply phi1'_star [(fresh_h, TyD.Ty_heap);
                                            (x, RefTy.toTyD t_x);
                                            (fresh_h_int, TyD.Ty_heap)] in 
          
          let pre_3 = VC.apply phi2_star [(fresh_h_int, TyD.Ty_heap)] in 
          let p_2_imp_3 = P.If (pre_2 , pre_3) in 
          let p_1_conj_2_3 = P.Conj (pre_1, p_2_imp_3) in 
          let var_binds_pre = [(fresh_h, TyD.Ty_heap )] in    
        (*∀h, x, h int
        * phi* h 
          * ∧(φ1 ′∗ )(h x h int )) =⇒ (φ2 ∗ ) h int*)
          let pre_phi = P.Forall (var_binds_pre, p_1_conj_2_3) in 
  
          (*create bind post
          * ∀h, x, h int , v, h ′ .(M1.li f t M φ1 ′ ) (h x h int ) ∧ (M2.li f t M φ2 ′ ) (h int v h ′ )*)
          let fresh_v = Var.get_fresh_var "v" in 
          let fresh_h' = Var.get_fresh_var "h'" in   
          
          let post_1 = VC.apply phi1'_star [(fresh_h, TyD.Ty_heap);
                                            (x, RefTy.toTyD t_x);
                                            (fresh_h_int, TyD.Ty_heap)] in 
          (*let post_1  = P.apply [(fresh_h, Var.fromString "h");(fresh_h_int, Var.fromString "h'");(fresh_x, Var.fromString "v")] phi1'_star in *)
          let post_2 = VC.apply phi2'_star [(fresh_h_int, TyD.Ty_heap);
                                              (fresh_v, RefTy.toTyD t2);
                                              (fresh_h', TyD.Ty_heap)] in 
          
          let post_conj = P.Conj (post_1, post_2) in
          
          let var_binds_post = [(fresh_h, TyD.Ty_heap);
                                 (fresh_v, RefTy.toTyD t2);
                                 (fresh_h', TyD.Ty_heap)] in 
          
          let post_phi = P.Forall (var_binds_post, post_conj) in 
          let bind_type = RefTy.MArrow (lubM, pre_phi, (fresh_v, t2), post_phi)in 
          (* let () = Printf.printf "%s" ("\n \n Type Synthesized for Bind "^(RefTy.toString bind_type)) in *)
          (gamma, delta, [], bind_type) 
     
     | RefTy.Uncurried (var_ty_list, bodyTy) -> 
          (* k is of the form (\[]. e or \) *)
          assert (List.length var_ty_list <= 1);
          match var_ty_list with 
            | [] -> 
                let RefTy.MArrow (e2, phi2, (v2, t2), phi2') = bodyTy  in 
                let lubM = (*M*)RefTy.lub_effects type_p1 bodyTy in
   
                 
                let fresh_h = Var.get_fresh_var "h" in 
                let fresh_h_int = Var.get_fresh_var "h_int" in 
                let fresh_bot_x = Var.get_fresh_var "x" in 

                (* Add the h_int and x as existenitials in env *)
                let gamma = VC.extend_gamma (fresh_h_int, RefTy.lift_base (TyD.Ty_heap)) gamma in 
                let gamma = VC.extend_gamma (fresh_bot_x, t1) gamma  in 

                (** TODO : lifting is not yet defined *)
                (* let lifted_ty1 = RefTy.liftM type_p1 lubM in 
                let lifted_ty2 = RefTy.liftM type_p2 lubM in 
                 *)
                let lifted_ty1 = type_p1 in 
                let lifted_ty2 = bodyTy in 


                (*what if the lifted is arrow*)      
                let RefTy.MArrow (lubM, phi1_star,(v1, t2) , phi1'_star) = lifted_ty1 in 
                let RefTy.MArrow (lubM, phi2_star,(v2, t2), phi2'_star) = lifted_ty2 in       
                      
                 
                (* create bind pre *)
                let pre_1 = VC.apply phi1_star [(fresh_h, TyD.Ty_heap)] in  
                let pre_2 = VC.apply phi1'_star [(fresh_h, TyD.Ty_heap);
                                                  (fresh_bot_x, RefTy.toTyD t1);
                                                  (fresh_h_int, TyD.Ty_heap)] in 
                
                let pre_3 = VC.apply phi2_star [(fresh_h_int, TyD.Ty_heap)] in 
                let p_2_imp_3 = P.If (pre_2 , pre_3) in 
                let p_1_conj_2_3 = P.Conj (pre_1, p_2_imp_3) in 
                let var_binds_pre = [(fresh_h, TyD.Ty_heap )] in    
               (*∀h, x, h int
                phi* h 
                * ∧(φ1 ′∗ )(h x h int )) =⇒ (φ2 ∗ ) h int*)
                let pre_phi = P.Forall (var_binds_pre, p_1_conj_2_3) in 
  
                (*create bind post
                * ∀h, x, h int , v, h ′ .(M1.li f t M φ1 ′ ) (h x h int ) ∧ (M2.li f t M φ2 ′ ) (h int v h ′ )*)
                let fresh_v = Var.get_fresh_var "v" in 
                let fresh_h' = Var.get_fresh_var "h'" in   
                
                let post_1 = VC.apply phi1'_star [(fresh_h, TyD.Ty_heap);
                                                  (fresh_bot_x, RefTy.toTyD t1);
                                                  (fresh_h_int, TyD.Ty_heap)] in 
                (*let post_1  = P.apply [(fresh_h, Var.fromString "h");(fresh_h_int, Var.fromString "h'");(fresh_x, Var.fromString "v")] phi1'_star in *)
                let post_2 = VC.apply phi2'_star [(fresh_h_int, TyD.Ty_heap);
                                                    (fresh_v, RefTy.toTyD t2);
                                                    (fresh_h', TyD.Ty_heap)] in 
                
                let post_conj = P.Conj (post_1, post_2) in
                
                let var_binds_post = [(fresh_h, TyD.Ty_heap);
                                       (fresh_v, RefTy.toTyD t2);
                                       (fresh_h', TyD.Ty_heap)] in 
                
                let post_phi = P.Forall (var_binds_post, post_conj) in 
                let bind_type = RefTy.MArrow (lubM, pre_phi, (fresh_v, t2), post_phi)in 
                (* let () = Printf.printf "%s" ("\n \n Type Synthesized for Bind "^(RefTy.toString bind_type)) in *)
                (gamma, delta, [], bind_type) 
               
            | (x, t_x) :: [] -> 
              let arrow_for_type_k = RefTy.Arrow ((x, t_x), bodyTy) in 
              synthesizeCombBind gamma sigma delta type_p1 arrow_for_type_k
          
     | _ -> raise (TypeSynthExc ("The continuation in a Bind Combinator must be an Arrow We have Type \n"^(RefTy.toString type_k)))             

 
open VerificationC
open TyD    
(*TODO :: The typing rules are defined over a Normalized AST for LambdaSyn.t
  We need a pre Normalising Phase *)

let rec synthesizeType (gamma : Gamma.t) (sigma:Sigma.t) (delta : Predicate.t)
    (t : Syn.monExp) : (Gamma.t * Predicate.t * VerificationC.t list * RefTy.t) = 
	    match t with 
    | Evar v -> 
        let type4v = try 
            Gamma.find gamma v 
        with 
          | e -> raise (TypeSynthExc ("Typechecking Evar : Type Missing, May be missed extending Gamma "^(v)))

        in  (gamma, delta, [], type4v)

    | Eval v -> 
        (match v with 
          | ILit i-> 
              let varv = Var.fromString "v" in 
              let varv_eq_i = P.Base (BP.varIntEq (varv, i))  in 
            (gamma, delta, [], RefTy.Base (varv, TyD.Ty_int, varv_eq_i ))
          | BLit b -> 
              let varv = Var.fromString "v" in 
              let varv_eq_b = P.Base (BP.varBoolEq (varv, b))  in 
              (gamma, delta, [], RefTy.Base (varv, TyD.Ty_bool, varv_eq_b ))

          | SLit s -> 
              let varv = Var.fromString "v" in 
              let varv_eq_s = P.Base (BP.varStrEq (varv, s))  in 
              (gamma, delta, [], RefTy.Base (varv, TyD.Ty_string, varv_eq_s ))

          | CLit c ->
              let varv = Var.fromString "v" in 
              let varv_eq_c = P.Base (BP.varCharEq (varv, c))  in 
             (gamma, delta, [], RefTy.Base (varv, TyD.Ty_char, varv_eq_c ))

          | Loc l -> 
              let type4v = try 
              Gamma.find gamma l 
              with 
              | e -> raise (SynthesisException "EApp Typechecking : Function Type Missing")
              in  (gamma, delta, [], type4v)
        )     


      | Elam (args, body) ->  (*this  deviates from the standard case *)
              (*all args will be Evars, so gamma' and delta' will remain 
               same as delta and gamma *)
              let _ = Printf.printf "%s" ("\n synthesizeType "^(Syn.monExp_toString t)) in 
              let vcs_args_types = 
                  List.map (fun iArg -> 
                              let (_, _,iVcs, iType) = synthesizeType gamma sigma delta iArg in 
                              (match iArg with 
                                | Evar iV -> (iVcs, iV, iType)
                                | _-> raise (TypeSynthExc "Lambda argument must be a variable") 
                              )
                            ) args in
              let (args2Type, gamma') = List.fold_left (
                                        fun (args2Type, gamma') (_, vi, ti)-> 
                                        (
                                           (vi, ti)::args2Type,
                                          (VC.extend_gamma (vi, ti) gamma')
                                          )
                                      ) ([], gamma) vcs_args_types in 

              let vcs' = List.fold_left (fun vcs' (vcsi,_,_) ->
                                        List.concat[vcsi;vcs']
                                        ) [] vcs_args_types in 

              let (gamma', 
                  delta', 
                  bodyVcs, 
                  bodyType
                 ) = synthesizeType gamma' sigma delta body in                        
              let lambdaType = RefTy.Uncurried (args2Type, bodyType) in 
              (* returns an updatd  *)
              (* let _ = Printf.printf "%s" (" Gamma After Elam "^(VC.string_gamma gamma')) in  *)
              (gamma', delta, List.concat[bodyVcs;vcs'], lambdaType)


      (*| Ematch (matchexp, caselist) typechecking case*)
      (*| Elet (bind, e1, e2)*)
      | Eret e -> 
          (match e with 
            | Evar v -> 
                  let type4v = try 
                      Gamma.find gamma v 
                   with 
                    | err -> raise err
                  in 
                synthesizeMonRet gamma delta e type4v 
              
            | _ -> raise (TypeSynthExc "Return statement only allows returning a var, assuming
                             A-normal form")
          )
      | Ebind (bind, e1, e2) ->
          (match bind with 
             | Evar v -> 
                let (gamma, delta, vcs4e1, type4e1) = synthesizeType gamma sigma delta e1 in 
                let () = Printf.printf "%s" ("\n Type for e1  "^(RefTy.toString type4e1)) in 
                let () = Printf.printf "%s" ("\n **************************************") in 
        
                let (gamma, delta, vcs4bind, type4bind) = synthesizeType gamma sigma delta bind in 
                let () = Printf.printf "%s" ("\n Type for bindvar  "^(RefTy.toString type4bind)) in 
                let () = Printf.printf "%s" ("\n **************************************") in 
        
                let gamma = VC.extend_gamma (v, type4bind) gamma in 
                let (gamma, delta, vcs4e2, type4e2) = synthesizeType gamma sigma delta e2 in 
                let () = Printf.printf "%s" ("\n Type for e2  "^(RefTy.toString type4e2)) in 
                let () = Printf.printf "%s" ("\n **************************************") in 
        
                let (gamma, delta, vcs, t) = synthesizeMonBind gamma delta type4e1 type4e2 v in 
                (gamma, delta, List.concat[vcs4e1;vcs4bind;vcs4e2; vcs], t)
                
                 
             | _ -> raise (TypeSynthExc "Bind variable in Monadic bind must be a var")
          )
      (*| Ecapp (fname, argslist) typechecking case *) 
      (* | Eskip  -> 

 *)
      | Eparser (cprim) ->
              let () = Printf.printf "%s" ("\n Parser Type Synthesis Case  ") in 
              synthesizeParserType gamma sigma delta cprim
    
      | Elet (bind, e1, e2) -> 
             (match bind with 
             | Evar v -> 
                let (gamma, delta, vcs4e1, type4e1) = synthesizeType gamma sigma delta e1 in 
                let gamma = VC.extend_gamma (v, type4e1) gamma in 
                let (gamma, delta, vcs4e2, type4e2) = synthesizeType gamma sigma delta e2 in 
                
                (gamma, delta, List.concat[vcs4e1;vcs4e2], type4e2)
                
                 
             | _ -> raise (TypeSynthExc "Bind variable in let exp must be a var")
          )
      
       | Ecapp (cname, argi_list) -> 
          let type4C = Sigma.find sigma cname in 
          let RefTy.Constructor (ti_list, ret_ty) = type4C in 
          assert (List.length argi_list == List.length ti_list);
          (*collect the VCs for each argument typechecking *)
          let vcs_argstc = 
                            List.fold_left2 
                                            (fun (vcs) argi typei -> 
                                              let (_,_,vcs_i, _) = checkType gamma sigma delta argi typei in 
                                              List.concat[vcs;vcs_i]
                                                  
                                                  ) [] argi_list ti_list
          in 

          (** Not doing any substitution for now, TODO later when unit testing*)
          (gamma, delta, vcs_argstc, ret_ty)  



      | Eapp (funExp, argsList) (*Eapp foo [x1, x2, x3,...xn] *) -> 
          let Evar funName = funExp in 
          
          let () = Printf.printf "%s" ("FunName "^(funName)) in 
          let funType = try 
                 Gamma.find gamma funName 
                with 
                  | e -> raise (SynthesisException "EApp Typechecking : Function Type Missing")
          in 
          (match funType with 
              | RefTy.Arrow ((_,_), _) -> 
                let uncurried = RefTy.uncurry_Arrow funType in 
                let RefTy.Uncurried (formalsList, retTy) = uncurried in
                (*create substitution (actuals, foramls)*)
                let formals = List.map (fun (vi, ti) -> vi) formalsList in 
                (*each arg in argsList will actuall be of the foram Evar 
                from the restriction of normal-forms
                *)
                (*
                  Γ ⊢ e𝑓 : (𝑥 : {𝜈 : t | 𝜙𝑥 }) → PE𝜀 {𝜙 } 𝜈 : t {𝜙 ′} Γ ⊢ x𝑎 : {𝜈 : t | 𝜙𝑥 }
                  ------------------------------------------------------------------------
                   Γ, [x𝑎/v]𝜙𝑥  ⊢ e𝑓 x𝑎 : [x𝑎 /𝑥]PE𝜀 {𝜙 } 𝜈 : t {𝜙 ′}
                *)
                                        
                let (actuals, delta, vcs) = List.fold_left2 
                                      (fun (a_i, d_i, vcs_i) xa_i x_i -> 
                                          let (fv_i, ft_i) = x_i in  
                                          let argi = Syn.componentNameForMonExp xa_i in 
                                          let argi_type = 
                                              try 
                                                Gamma.find gamma argi 
                                              with 
                                                | e -> raise (SynthesisException "EApp Typechecking : Argument Type Missing")
                                          in 
                                          
                                          let (bv_x, phi_x) = 
                                               match argi_type with 
                                                | RefTy.Base (bv,_, phi_x) -> (bv, phi_x) 
                                                | _ -> raise (SynthesisException ("EApp Typechecking : Argument Type Must be base, found Arg"^(argi)^" :: "^(RefTy.toString argi_type)))
                                          in        

                                          let vcs_arg_well_type_i = VC.fromTypeCheck gamma [delta] (argi_type, ft_i)  in 
                                          
                                          let phi_x_subs = Predicate.applySubst (argi, bv_x) phi_x in 
                                          (a_i@[argi], Predicate.Conj (d_i, phi_x_subs), vcs_i@[vcs_arg_well_type_i])
                                        )  ([], delta, []) argsList formalsList in 

                (* let _ = Printf.printf "%s" ("\n Done Extension "^(Predicate.toString delta)) in  *)
                

                                
                                              
                
                let subs = List.combine actuals formals in 
                (*create the type [actuals/foramls] retTy*)
                
                
                let appType = RefTy.applySubsts subs retTy in 

                let _ = Printf.printf "%s" ("\n Ret Type "^(RefTy.toString appType)) in 
                (*the subtyping check*)

                (* let vc = VC.fromTypeCheck gamma [delta] (appType, spec) in  *)

                (*make a direct call to the SMT solver*)
                (* let vcStandard = VC.standardize vc in 
                let () = Printf.printf "%s" ("\n $$$$$$$$$$$$$$$ "^VC.string_for_vc_stt vcStandard) in  
                let result = VCE.discharge vcStandard  in 
                let typechecks = 
                  match result with 
                  | VCE.Success -> true
                  | VCE.Failure -> false
                  | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                in 
                if (typechecks) then 
                 *)  
                (gamma, delta, vcs , appType)
               
              | _ -> raise (SynthesisException ("Funtype must be t1 -> t2, but found "^(RefTy.toString funType)))
             )        

      | Eite (cond, tbr, fbr) ->
              (*TODO :: Complete this implementation, then test count n *)
              (*Γ ⊢ e ⇒ (A 1 + A 2 )
                Γ, x 1 : A 1 ⊢ e 1 ⇒ B
                Γ, x 2 : A 2 ⊢ e 2 ⇒ B
                -------------------------------
                Γ ⊢ case(e, inj 1 x 1 . e 1 , inj 2 x 2 . e 2 ) ⇒ B *)         
              (* let (gamma, delta, condvc, condty) = synthesizeType gamma sigma delta e1 in  *)
                let (gamma, delta, vcs4e1, condTy) = synthesizeType gamma sigma delta cond in 
                let branchPredicate = 
                          match condTy with 
                            | RefTy.Base (v, t, p) -> 
                                  assert (TyD.sametype t TyD.Ty_bool);
                                  p

                            | _ -> raise (SynthesisException "Allowed Branch condition : Base Type")
                in 
                let delta_true = Predicate.Conj (delta, branchPredicate) in 
                let delta_false = Predicate.Conj (delta, Predicate.Not (branchPredicate)) in 
                
                let (gamma_true, delta_true, vcs_true, typeTrue) = 
                      synthesizeType gamma sigma delta_true tbr in 
                let (gamma_false, delta_false, vcs_false, typeFalse) = 
                      synthesizeType gamma sigma delta_false fbr in 
                
                (** *)
              
                let unified_type = unifyWithDisj typeTrue typeFalse in 
                (gamma@gamma_true@gamma_false, delta, [], unified_type)

           
           
      (*TODO :: 
        Add rules for Edo, Edref, Eref, Eassign 
      *)     
      
      | Edo (dobody, doret) ->
           (* do { x1 <- action1
            ; x2 <- action2
            ; mk_action3 x1 x2 ;
            doret};

           action1
         >>=
        (\ x1 -> action2
           >>=
         (\ x2 -> mk_action3 x1 x2 ))    *)

        let rec translate_do block_list = 
            match block_list with 
              [] -> doret 
              | (bvi, actioni) :: xs -> 
                    Eparser (Bind (actioni, Elam ([bvi], translate_do xs)))

        in 
        let translated = translate_do dobody in 

        let _ = Printf.printf "%s" ("\n  Translated  "^(Syn.monExp_toString translated)) in  

        synthesizeType gamma sigma delta translated

      | _ ->
        (*Eref case *)
        let _ = Printf.printf "%s" (" Mon EXP "^(Syn.monExp_toString t)) in  
        (*TODO :: Implement the ITE case *)
        raise (TypeSynthExc "Unimplemented Typesynthesis")
 
and  synthesizeDerivedType (gamma : Gamma.t) (sigma:Sigma.t) (delta : Predicate.t)
    (t : Syn.parserDerived) : 
      (Gamma.t * 
       Predicate.t * 
      VerificationC.t list * 
      RefTy.t) = 

    match t with 
      | Any plist ->
          raise (TypeSynthExc "Unimplemented Derived")
          (* let p1 = List.hd plist in 
          let (gamma, delta, vcsp1, typ1) = synthesizeParserType gamma sigma delta p1 in 
          let rec iterate gamma delta altTerm acc_vcs acc_type remaining = 
            match remaining with 
              | [] -> (gamma, delta, acc_vcs, acc_type)
              | x :: xs -> 
                 synthesizeParserType Alt (altTerm)   *)

      | _ -> raise (TypeSynthExc "Unimplemented Derived")


and  synthesizeParserType (gamma : Gamma.t) (sigma:Sigma.t) (delta : Predicate.t)
    (t : Syn.parserPrim) : 
      (Gamma.t * 
       Predicate.t * 
      VerificationC.t list * 
      RefTy.t) = 
      let () = Printf.printf "%s" ("\n Synthesizing Type for Parser "^(Syn.parserPrim_toString t)) in      
      match t with 
        | Var v -> 
          let vtype = 
              try 
                Gamma.find gamma v 
              with 
                | e -> raise (TypeSynthExc "No type found for a Var bound parser")
           in        
          (gamma, delta, [], vtype)
        | Eps -> 
            
            let h = Var.fromString "h" in 
            let h' = Var.fromString "h'" in 
            let v = Var.fromString "v" in 

            let pre = Predicate.Forall ([(h, TyD.Ty_heap)], Predicate.True) in 
            let post = Predicate.Forall ([(h, TyD.Ty_heap); 
                                          (v, TyD.Ty_unit); 
                                          (h', TyD.Ty_heap)], 
                                                P.Base (BP.Eq (BP.Var h, BP.Var h'))) in 

            (gamma, delta, [], RefTy.MArrow (Effect.Pure, pre, (v, RefTy.lift_base (TyD.Ty_unit)), post))                                     


        | Bind (p1 , k) -> 
              
              
              let _ = Printf.printf "%s" ("\n Synthesizing Bind Parser "^(Syn.parserPrim_toString t)) in              
              let (gamma, delta, vcs1, type4p1) = synthesizeType gamma sigma delta p1 in 
              Printf.printf "%s" ("\n Bind First Component Done "^(Syn.monExp_toString p1));
              Printf.printf "%s" ("\n Has Type : "^(RefTy.toString type4p1));
              
              Printf.printf "%s" ("\n Continuation : "^(Syn.monExp_toString k));

              (* let RefTy.MArrow (_, _, (vi, ti), _) = type4p1 in 
               *)
              let p1RetType = 
                match type4p1 with 
                    | RefTy.MArrow (_, _, (_, ti), _) -> ti
                    | RefTy.Base (_,_,_) -> type4p1
              in       
                  
              let gamma = match k with 
                        | Elam (fargs, k_body) -> 
                              assert (List.length (fargs) <= 1);
                              if (List.length fargs == 1) then 
                                let Evar ai = List.hd fargs in 
                                (VC.extend_gamma (ai,  p1RetType) gamma)
                              else 
                                (gamma)
                        | _ -> raise (TypeSynthExc "Parser Bind continuation Illformed , must be a fun")
              in 
              let (gamma, delta, vcs2, type4k) = synthesizeType gamma sigma delta k in 

              (*FIXME :: The bound variable in the continuation is not in the gamma 
              Check
              test : number >>= \x. content *)
              Printf.printf "%s" ("\n Continuation Synthesis Done For "^(Syn.monExp_toString k)^"\n "^(RefTy.toString type4k));             
              (match type4k with 
                | RefTy.Arrow ((_,_),_) ->     
                       let (gamma, delta, vcs3, bindType) = 
                        synthesizeCombBind gamma sigma delta type4p1 type4k in 
                        Printf.printf "%s" ("\n Type for Bind Parser "^(Syn.parserPrim_toString t));
                        Printf.printf "%s" ("\n "^(RefTy.toString bindType));
                        
                     
                      (gamma, delta, List.concat [vcs1;vcs2;vcs3], bindType) 
                | RefTy.Uncurried (_, _) -> 
                    let (gamma, delta, vcs3, bindType) = 
                        synthesizeCombBind gamma sigma delta type4p1 type4k in 
                        Printf.printf "%s" ("\n Type for Bind Parser "^(Syn.parserPrim_toString t));
                        Printf.printf "%s" ("\n "^(RefTy.toString bindType));
                       
                      (gamma, delta, List.concat [vcs1;vcs2;vcs3], bindType) 
                    
                | _ -> 
                
                raise (TypeSynthExc ("The continuation in a Bind combinator must be an Arrow "^(RefTy.toString type4k)))
              )
        | Char c ->

            (**Stexc {\forall h. True} v : char_result {\forall h v h'.
                                              Inl x => x = c && includes h' h inp} 
                                              && Inr err => includes h' h inp*) 
            let h = Var.fromString "h" in 
            let h' = Var.fromString "h'" in 
            let v = Var.fromString "v" in
           
            let pre = Predicate.Forall ([(h, TyD.Ty_heap)], Predicate.True) in 
            
            (*includes h' h inp = true*)
            let relExprTrue = RelLang.V (Bool true) in 
             
            let includes = P.Rel (
                                  RP.Eq (
                                  RelLang.MultiR ((RelLang.instOfRel (RelId.fromString "includes")), 
                                  [h';h;Var.fromString "inp"] ),
                                  relExprTrue)
                                  ) 
                                  in 
            (* v = c *)
            let v_eq_c =  P.Base (BP.varCharEq (v, c)) in                     
            let (existential_var, post_success) = exc_success_predicate (v, TyD.Ty_char) 
                                                ("Inlchar")(Predicate.Conj (v_eq_c, includes)) in 
            (* let gamma = VC.extend_gamma (existential_var, RefTy.lift_base (TyD.Ty_string)) gamma in  *)

            let post_failure =  exc_failure_predicate (v, "CErr") ("Inrchar") includes in 
            let post = Predicate.Forall ([(h, TyD.Ty_heap); 
                                          (v, TyD.fromString "char_result"); 
                                          (h', TyD.Ty_heap)], 
                                                Predicate.Forall 
                                                  ([(existential_var, TyD.Ty_string)],
                                                    Predicate.Conj (post_success, post_failure))) in 

            let resTy = RefTy.fromTyD (TyD.fromString "char_result") in 
            (gamma, delta, [], RefTy.MArrow (Effect.StExc, pre, (v, resTy), post))                                     

        | Bot -> 
            (**-----------------------------------
               \Gamma, .... |- bot : Exc {true} v : result {v = Inr err && h' = h} *)  
            let h = Var.fromString "h" in 
            let h' = Var.fromString "h'" in 
            let v = Var.fromString "v" in 

            let pre = Predicate.Forall ([(h, TyD.Ty_heap)], Predicate.True) in 
            
            let h_eq_h' = P.Base (BP.varEq (h', h)) in
            let post_failure =  exc_failure_predicate  (v, "Err") ("Inr") h_eq_h' in 

            let post = Predicate.Forall ([(h, TyD.Ty_heap); (v, TyD.fromString "result"); (h', TyD.Ty_heap)], 
                                          post_failure) in 
             let resTy = RefTy.fromTyD (TyD.fromString "result") in 
           
            (gamma, delta, [], RefTy.MArrow (Effect.Exc, pre, (v, resTy), post))


            


        | Alt (p1, p2) -> 
            let (gamma, delta, vcs1, type4p1) = synthesizeParserType gamma sigma delta p1 in 
            Printf.printf "%s" ("\n Synthesis of First choice  DONE "^(Syn.parserPrim_toString p1));
            let (gamma, delta, vcs2, type4p2) = synthesizeParserType gamma sigma delta p2 in 
            Printf.printf "%s" ("\n Synthesis of Second choice  DONE "^(Syn.parserPrim_toString p2));
            
            let (gamma, delta, vcs3, typealt) = 
            synthesizeCombAlt gamma  sigma delta type4p1 type4p2 in  
             (gamma, delta, List.concat[vcs1;vcs2;vcs3], typealt) 
        
        | Map (f ,p) ->
            let (gamma, delta, vcs4f, type4f) = synthesizeType gamma sigma delta f in
            (match type4f with 
              | RefTy.Arrow ((x,t_x), ret_ty) -> 
                   let (gamma, delta, vcs4p, type4p) = synthesizeParserType gamma sigma delta p in 
                   let RefTy.MArrow (eff,pre, (v, t_v), post) = type4p in 
                   assert (RefTy.compare_types t_x t_v);
                   (gamma, delta, List.concat[vcs4f;vcs4p], 
                    RefTy.MArrow (eff, pre, (v, ret_ty), post))
              | _ -> raise (TypeSynthExc "the argument to Map combinator must be a functions")
            )
        | Fix funct ->
            (*  let typefunct = funct.ofType in 
             let codefunct = funct.expMon in 
             *)
             (match funct with 
               | Elam (xs, bodyExp) -> 
                  assert (List.length xs == 1);
                  let x = List.hd xs in
                  (match x with 
                    | Evar xVar -> 
                        let () = Printf.printf "%s" ("\n VarArgument  "^xVar) in 
                        let typeX =  
                            try
                              Gamma.find gamma xVar 
                            with 
                              | e -> raise (TypeSynthExc "The argument to fix must be provided 
                                             a type" )
                        in 
                       let gamma = VC.extend_gamma (xVar, typeX) gamma in 
                       let (gamma, delta, vcs, bodyType) = checkType gamma sigma delta bodyExp typeX in 
                       let () = Printf.printf "%s" ("\n Body Type For Fix  "^(RefTy.toString bodyType)) in 
                      (gamma, delta, vcs, bodyType) 
                  ) 
               | _ -> raise (TypeSynthExc "Argument to function must be a typed Lambda")     

             )

        | Ret v -> 
              let (gamma, delta, vcs4v, type4v) = synthesizeType gamma sigma delta v in 
              let h = Var.fromString "h" in 
              let h' = Var.fromString "h'" in 
              let v = Var.fromString "v" in 

              let pre = Predicate.Forall ([(h, TyD.Ty_heap)], Predicate.True) in 
              let post = Predicate.Forall ([(h, TyD.Ty_heap); (v, TyD.Ty_unit); (h', TyD.Ty_heap)], 
                                                P.Base (BP.Eq (BP.Var h, BP.Var h'))) in 
              (gamma, delta, vcs4v, RefTy.MArrow (Effect.Pure, pre, (v, type4v), post))                                     
        | Der dp -> 
              synthesizeDerivedType gamma sigma delta dp 


(*
  build a typechecker for the given monExp term in the language
  \Gamma, \Delta |-_(\sigma) e : ( \Gamma', \Delta', \spec)
  Just the checking for the fun application
 Note : Current version works by checking the types and returning given type if generated VCs are dishcarged
 *)
and checkType (gamma : Gamma.t) (sigma:Sigma.t) (delta : Predicate.t)
    (t : Syn.monExp) (spec : RefTy.t) : (Gamma.t * Predicate.t * VerificationC.t list * RefTy.t) = 
	  
    let () = Printf.printf "%s" ("\n Typechecking "^(Syn.monExp_toString t)) in 
     match t with 
      | Elam (args, body)  ->  
         (* the checkable type must be an arrow*)
          (match spec with 
           | RefTy.Arrow ((vi,ti),tb) -> 
                (* checkLambda *)
                let uncurried = RefTy.uncurry_Arrow spec in 
                let RefTy.Uncurried (formals, bodyType) = uncurried in 
                assert (List.length args == List.length formals);
                
                (* Assumed no alpharenaming bw the name for args and formals in spec  *)
                let gamma' = List.fold_left (fun g' (vi, ti)-> 
                                      VC.extend_gamma (vi, ti) g') gamma formals in 

                let (gamma', delta', vcs, bty) = checkType gamma' sigma delta body bodyType in 
                (gamma', delta, vcs, RefTy.Arrow ((vi, ti), bty))                     

           | _ -> raise (TypeSynthExc "Given type for a lambda term must be an Arrow")
          )

      | Ematch (matchexp, caselist) -> 
          let type4matchexp = synthesizeType gamma sigma delta matchexp in 
          
          let extendedGammai g casei =
              let {constructor;args;exp} = casei in 
              (* Ci : t1 * t2 .... * tk -> t \in Sigma *)
              let type4Ci = Sigma.find sigma constructor in 
              let () = Printf.printf "%s" (" Constructor Type "^(RefTy.toString type4Ci)) in 
              
              let RefTy.Arrow ((_, Tuple argstypelist), exptype) = type4Ci in 
              (* let RefTy.Constructor (argstypelist, exptype ) = type4Ci in  *)
              assert (List.length args == List.length argstypelist);
              let args_type_list = List.map2 (fun vi ti -> 
                                (vi, ti)) args argstypelist in 
              List.fold_left (fun g (vi, ti) -> VC.extend_gamma (vi, ti) g) gamma args_type_list
          in 

          let ciexp_vc_type_list = List.map 
                                (
                                fun ci -> 
                                let exp = ci.exp in 
                                let gammai = extendedGammai gamma ci in 
                                let (_,_, vcsi, tyi) = checkType gammai sigma delta exp spec in 
                                (vcsi, tyi)                  
                                )  caselist
          in 



          let (hd, rest) = (List.hd ciexp_vc_type_list, List.tl ciexp_vc_type_list) in 
        
          let (vcs, unified) = List.fold_left 
                                  (fun (vcs, unified) (vcs_i, type_i) ->
                                        (List.concat[vcs_i;vcs], 
                                          unifyWithDisj unified type_i)  
                                  )hd rest in 

        (gamma, delta, vcs, unified)
  
          (* join the type of each case expressions *)
        
     
      | _ -> 
        let () = Printf.printf "%s" ("\n The other case "^(Syn.monExp_toString t)) in 
        let (gamma, delta, vcs, syntype) = synthesizeType gamma sigma delta t in 
        
        (* let () = Printf.printf "%s" ("\n Gamma  "^(VC.string_gamma gamma)) in  *)
        
        let () = Printf.printf "%s" ("\n Synthesized a Type Other Case  "^(RefinementType.toString syntype)) in 
        
        let () = Printf.printf "%s" ("\n Given Type Other Case  "^(RefinementType.toString spec)) in 
        
        let vc = VerificationC.fromTypeCheck gamma [delta] (syntype, spec) in 
        (gamma, delta, vc::vcs, syntype)
       
  
(*
\Gamma (x) = {v : t | phi}
ret : x : t -> M {true} v : t {\forall h v h'. h' = h /\ v = x /\ phi (v)}*)
and synthesizeMonRet  (_Gamma: VerificationC.vctybinds) 
              (delta : Predicate.t) 
              (e : Syn.monExp)
              (x_ty : RefTy.t) : 
              (Gamma.t * 
                Predicate.t * 
                VerificationC.t list * 
                RefTy.t
              )= 
              match e with 
                  | Evar var_x ->       
                      
                      match x_ty with 
                        | RefTy.Base (bv, t, phi) -> 
                             let _ = Printf.printf "%s" ("\n Type for ret Var "^(RefTy.toString x_ty)) in 
                             let x_tyd = RefTy.toTyD x_ty in 
                            (*Create Bounded new type*)
                             (*no type inference so need to provide the type for the bound variable of a formula*)
                             let bv_h = Var.get_fresh_var "h" in 
                             let bv_v = Var.get_fresh_var "v" in 
                             let bv_h' = Var.get_fresh_var "h'" in 

                             let pre =  P.Forall ([(bv_h, Ty_heap)], P.True) in 
                             let post_conjunct1 = P.Base (BP.Eq (BP.Var bv_h, BP.Var bv_h')) in 
                             let post_conjunct2 = P.Base (BP.Eq (BP.Var bv_v, BP.Var var_x)) in 
                             let post_conjuntc3 = P.applySubst (bv_v, (Var.fromString "v")) phi in 
                
                             let local_var_binds = [(bv_h, Ty_heap);(bv_v, x_tyd);(bv_h', Ty_heap) ] in 

                             let post = P.Forall (local_var_binds, P.Conj (post_conjunct1, 
                                                                            P.Conj (post_conjunct2, post_conjuntc3))) in       

                             let retType = RefTy.MArrow (Effect.Pure, 
                                                 pre , (bv_v, x_ty), post) in      

                             (_Gamma, delta, [], retType)   
                        | _ -> raise (TypeSynthExc "Unhandled Case return an effectful computation")     
                  | _ -> raise (TypeSynthExc "Eret only allowed with variables, e.g. retrun v \n 
                                    Assuming A-normal form")     

(*The bind rule in lambda_eff*)
and synthesizeMonBind
              (acc_gamma: Gamma.t) 
              (acc_delta : Predicate.t) 
              (acc_type: RefTy.t) 
              (ci_type :RefTy.t)
              (bvi : Var.t) : 
              (Gamma.t * Predicate.t * VerificationC.t list *  RefTy.t) = 
     match (acc_type, ci_type) with 
      | (RefTy.MArrow (eff1, phi1, (v1,t1), phi1') , RefTy.MArrow (eff2,phi2, (v2, t2), phi2')) -> 
              
                let fresh_h_int = Var.get_fresh_var "h_int" in 
                let _Gamma = VC.extend_gamma (fresh_h_int, (RefTy.lift_base Ty_heap)) acc_gamma in 
                let bv_x = Var.get_fresh_var "x" in 
                let _Gamma = VC.extend_gamma (bv_x,  t1) _Gamma in  
                

                
                (*Create Bounded new type*)
                (*no type inference so need to provide the type for the bound variable of a formula*)
                let bv_h = Var.get_fresh_var "h" in 
                (* let _Gamma = VC.extend_gamma (bv_h, (RefTy.lift_base Ty_heap)) _Gamma in  *)
                let bv_h' = Var.get_fresh_var "h'" in 
        
        	      (*Following type is now created in this extended environment*)
                (*\forall x, h_int. ( \phi1') h x h_int => \phi2 h_int x)*)
                        
               
                 
                (*phi1 h*)
                let f1_pre = (VC.apply phi1 [(bv_h, Ty_heap)]) in 
                

                (* We do not SP (P, pi) => Pre as this is checked separately in hoarePre Check *)   
                (* let f2_pre =  P.If ((VC.apply phi1' [(bv_h, Ty_heap); (bv_x, RefTy.toTyD t1); (fresh_h_int, Ty_heap)]), 
                                    ((VC.apply phi2 [(fresh_h_int, Ty_heap)]))
                                                  ) *)
                                            
                                        
                                     

                
(* 
                let bind_pre (*create pre-condition*) =  P.Forall ([(bv_h, Ty_heap)], P.Conj (f1_pre, f2_pre))  in  *)
                  
               let bind_pre (*create pre-condition*) =  P.Forall ([(bv_h, Ty_heap)], (f1_pre))  in 
               
                (*creating post*)
                (*forall v h h' x h_int. phi1 x h h_int*)
                let (bv_v)= Var.get_fresh_var "v" in 
                (* let _Gamma = VC.extend_gamma (bv_v,  t2) _Gamma in  *)
                
                (*
                  This is an ungly hack, as we do not define a type for let x = e1 in e2
                  Add the the result var bvi in bv1 <- M2 .. to the env, if the second computation is
                  return x, then there is no bound var *)
                let _Gamma = 
                  if (Var.toString bvi = "skip") then 
                    _Gamma
                  else 
                    VC.extend_gamma (bvi, t2) _Gamma 

                  in 
                  
                (*Add h' to the Gamma*)

(*                 let () = 
                Printf.printf "%s" ("\n POST NON APPLIED "^(P.toString phi2')) in 
 *)             
                let local_var_binds = [(bv_h, Ty_heap);(bv_v, RefTy.toTyD t2);(bv_h', Ty_heap) ] in 
                let post_conjuntc1 = ( VC.apply phi1' [(bv_h, Ty_heap);(bv_x, RefTy.toTyD t1);(fresh_h_int,Ty_heap)]) in 
                (*binding of the variable and the return variable*)
                let post_conjuntc2 = (VC.apply phi2' [(fresh_h_int ,Ty_heap);(bv_v, RefTy.toTyD t2); (bv_h', Ty_heap)]) in 
                
                  (*\forall bind_post. we shoud also have [bv_i/bv_v]bind_post *)

               
                (* let bind_ret = P.applySubst (bvi, bv_v) post_conjuntc2 in 
                 *)
                  
                let bind_ret = 
                 if (Var.toString bvi = "skip") then 
                   P.True
                  else 
                    P.Base (BP.Eq (BP.Var bvi, BP.Var bv_v)) 
                  
                in 



                
               (*  let post_conjuntc3 = Predicate.reduce (bvi, bv_v) post_conjuntc2 in 
                *) 
               let bind_post (*create post-condition*) = 
                if (Var.toString bvi = "skip") then 
                  P.Forall (local_var_binds, P.Conj (post_conjuntc1, post_conjuntc2))
                else 
                    P.Forall (local_var_binds, P.Conj 
                      (P.Conj (post_conjuntc1, post_conjuntc2), bind_ret))
               in 

                (*least uppper bound*)
                let lubM = Effect.lub eff1 eff2  in                 
                let new_acc_ty = RefTy.MArrow (lubM, bind_pre , (bv_v,t2), bind_post) in
                
                
                
              (*clean up the gamma*)
                let bv_phi1 = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi1) in 
                let bv_phi1' = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi1') in
                let bv_phi2 = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi2) in
                let bv_phi2' = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi2') in

              
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi1 in 
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi1' in 
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi2 in 
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi2' in 

               (*  let () = Printf.printf "%s" (" \n \n \n >>>>>>>>>>>>>>>>>>>>>>>>>> GAMMA AFTER REMOVAL  "^(string_of_int (List.length _Gamma))^" = "^(string_gamma _Gamma)) in  
                *) 
                (_Gamma, acc_delta, [], new_acc_ty)
                        
                
      | (RefTy.MArrow (eff1, phi1, (v1,t1), phi1') , RefTy.Base (vbase, tbase, phibase)) -> 
            let _Gamma = acc_gamma in 
       


            let bv_h = Var.get_fresh_var "h" in 
            (* let _Gamma = VC.extend_gamma (bv_h, (RefTy.lift_base Ty_heap)) _Gamma in  *)
            let bv_x = Var.get_fresh_var "x" in 
            
            let ret_ty_subs = RefTy.applySubsts [(bv_x, vbase)] ci_type in 
            
            let _Gamma = VC.extend_gamma (bv_x, ret_ty_subs) _Gamma in 
            let bv_h' = Var.get_fresh_var "h'" in 
            (* let _Gamma = VC.extend_gamma (bv_h', (RefTy.lift_base Ty_heap)) _Gamma in  *)
            
            let res_pre = VC.apply phi1 [(bv_h, Ty_heap)] in 
            
            let res_phibase = P.reduce (bv_x, vbase) phibase in 
            
            let res_post  = VC.apply phi1' [(bv_h ,Ty_heap);(v1, RefTy.toTyD t1); (bv_h', Ty_heap)]  in 
            
            let res_post = P.Conj (res_post, res_phibase) in

            let bind_pre (*create pre-condition*) =  P.Forall ([(bv_h, Ty_heap)], res_pre)  in 
                
            let local_var_binds = [(bv_h, Ty_heap);(bv_x, tbase);(bv_h', Ty_heap) ] in 
                
            let bind_post (*create post-condition*) = 
                 P.Forall (local_var_binds, res_post)  in 

              let lubM = eff1  in                 
              let new_acc_ty = RefTy.MArrow (lubM, bind_pre , (bv_x, ci_type), bind_post) in
        
                (*clean up the gamma*)
                let bv_phi1 = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi1) in 
                let bv_phi1' = List.map (fun (vi, ti) -> vi) (Predicate.getBVs phi1') in
                
              
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi1 in 
                let _Gamma = List.fold_left (fun _gamma vi -> VC.remove_from_gamma vi _gamma) _Gamma bv_phi1' in 
                


             (_Gamma, acc_delta, [], new_acc_ty)
                
    

      | (_, _) -> raise (SynthesisException ("Mon-bind :: binding non copmputations "^(RefTy.toString acc_type)^(" >>= ")^(RefTy.toString ci_type)^" \n"))     





