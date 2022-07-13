open Lambdasyn
open SpecLang
open Lib
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 


let indentation t = 
    indentT  t 
(* isAligned : int -> bool *)
let isAligned i = 
    Elet (Evar "u", (apply "getState" []), 
        Elet (Evar "b", apply "equalint" [Evar "u", Evar "i"]),
        Eite (b, 
              Eret (Ibool true),
              Eret (Ibool false))
     )

(* isIndented :: i :: Int -> {v : Parser Bool | v = true <=> i > (minInd (sel h user)) && i <= maxInd (sel h user)} *)
(* isIndented :: Int -> Parser Bool
isIndented i = 
     do 
        u <- getState    
        let min = minind u in 
            let max = maxind u in   
            if (min < i) && (i <= max) then return True else  return False *)

let isIndented i =  
        Elet (Evar "u", (apply "getState" []), 
                Elet (Evar "b", apply "greaterint" [Evar "u", Evar "i"]),
            Eite (b, 
              Eret (Ibool true),
              Eret (Ibool false))
        )
   


(* {-caseexp :  State { top (brace_ist (sel h ist)) = I } 
                v : Tree I 
            {
             top (brace_ist (sel h' ist)) = I' /\ 
             I' > I /\   
             sel h' inp C= sel h inp} 
-} *)
(* caseexp :: Parser Tree
caseexp = 
          do 
            ct <- offsideString "case" 
            e <- offsideExp 
            ot <- offsidestring "of"
            {-error ot <- string "of" -}
           alts <- offsidealts
          
         Node "case" (indentation ct) ([ct,e,ot]++alts) )))) -}
 *)


(* caseexp :  State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : offsideTree I |  true} 
	        {\(h : heap), (v : offsideTree I), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            I' = I /\ 
            sel(h', inp) C= sel(h, inp))
            };  *)

let caseexp = dostmt 
              [ct <- apply "offiseString" ["case"];
              e <- offisdeExp;
              ot <- apply "offiseString" ["case"];
              alts <- offsidealts;
              Elet 
              (Evar "children", concat [[ct];[e];[ot];[alts]],   
                 Ecapp (Evar "Tree", [SLit "case"; 
                                   Eapp (Evar "indentation", [Evar "ct"]),
                                   Evar "children"]))
                 ]                         


(*
offsideString : (s : { v : string | true}) -> 
           State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : offsideTree I |  true} 
	        {\(h : heap), (v : offsideTree I), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            ( I' = I /\
            node (v) = s /\
            sel (h', inp) C= sel (h, inp)
            )
            }; 
 *)
let offsideString s = 
    let fstpart = dostmt [assign "p" (apply "getPosition", []);
                          assign "x" (apply "sourceColumn", [Evar "p"])
                         ] in 
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]), 
                    Eite (Evar "check",
                            (apply "string" [Evar "s"] >>= 
                                    Elam (Evar "y", 
                                        Ecapp (Evar "Tree", 
                                        [Evar "y"; 
                                        Evar "x";
                                        Evar "nil"])
                                    )

                            ),
                            (*Else *)
                            Eret (Eparser Bot)


                )
                ) 
      in 
      fstpart sndpart                            

(* {- offsideExp : s : String ->  
            State {top (brace_ist (sel h ist)) = I } 
            v : Tree I 
            { node (v) = s /\ 
              indent (v) = offset (sel h inp) /\   
              sel h' inp C= sel h inp} 
-} *)
let offsideExp = offside_identifier <|> offside_number

(* offsideidentifier : State {top (brace_ist (sel h ist)) = I } 
            v : {v : Tree [char] I} 
            { indent (v) = offset (sel h inp) /\   
              sel h' inp C= sel h inp} 
  
*)
(* offside_identifier :: Parser Tree
offside_identifier = 
    do 
        p <- getPosition
        x <- sourceColumn
        if (isIndented x) then 
            identifier >>= (\y -> return Leaf y x) 
        else 
            parserFail "offside rule not satisfied in identifier"     *)

let offside_identifier = 
    let fstpart = dostmt [assign "p"  (apply "getPosition", []);
                          assign "x"  (apply "sourceColumn", [Evar "p"])] in 
    
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]), 
                    Eite (Evar "check",
                            (apply "string" [Evar "s"] >>= 
                                    Elam (Evar "y", 
                                        Ecapp (Evar "Tree", 
                                        [SLit "identifier"; 
                                        Eapp (Evar "indentation", [Evar "y"]),
                                        Evar "nil"])
                                    )

                            ),
                            (*Else *)
                            Eret (Eparser Bot)


                )
                ) 
    
      in 


      fstpart sndpart                            



(* 
{- offsideidnumber : State {top (brace_ist (sel h ist)) = I } 
            v : Tree int I 
            { indent (v) = offset (sel h inp) /\   
              sel h' inp C= sel h inp} 
-} *)
(* let offside_number =    
     do 
        p <- getPosition
        x <- sourceColumn
        if (isIndented x) then 
            number >>= (\y -> return Leaf "number" x) 
        else 
            parserFail "offside rule not satisfied in number"     *)



let offside_number = 
    let fstpart = dostmt [assign "p"  (apply "getPosition", []);
                          assign "x"  (apply "sourceColumn", [Evar "p"])] in 
    
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]), 
                    Eite (Evar "check",
                            (apply "string" [Evar "s"] >>= 
                                    Elam (Evar "y", 
                                        Ecapp (Evar "Tree", 
                                        [SLit "number"; 
                                        Eapp (Evar "indentation", [Evar "y"]),
                                        Evar "nil"])
                                    )

                            ),
                            (*Else *)
                            Eret (Eparser Bot)


                )
                ) 
    
      in 


      fstpart sndpart                            



(* 
{- aligned_alts : State {top (brace_ist (sel h ist)) = I } 
            v : [Tree exp I] 
            { aligned minI v && 
            sel h' inp C= sel h inp} 
-} *)
(* 

aligned_alts :: Parser [Tree]
aligned_alts = 
   do      
        p <- getPosition 
        x <- sourceColumn
        if (isIndented x) then 
            do 
                alt1 <- offside_alt 
                _ <- setIndentation x 
                _ <- setAbsolute True
                alts <- many1 offside_alt
                _ <- setAbsolute False
                return (alt1 :: alts) *)
        
            

let aligned_alts = 
    let fstpart = dostmt [assign "p"  (apply "getPosition", []);
                          assign "x"  (apply "sourceColumn", [Evar "p"])] in 
    
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]), 
                    Eite (Evar "check",
                            many1 offside_alt,
                            (*Else *)
                            Eret (Eparser Bot)


                        )
                    ) 
      in 
      fstpart sndpart                            



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
            let annotated = Gamma.find gamma "caseexp" in    
             let () = Printf.printf "%s" ("\n ********Annotated*********\n  "^(RefinementType.toString annotated)) in 
            R.verifyRParser gamma sigma delta caseexp annotated
        with 
            | e -> 
                raise (e);
                let (gamma, delta, vc, refty) = STC.synthesizeType gamma sigma delta caseexp  in 
                Printf.printf "%s" (RefinementType.toString refty)
                   
  else 
        raise (CompilerExc ("Required 1 args provided "^(string_of_int num_args)))  
  