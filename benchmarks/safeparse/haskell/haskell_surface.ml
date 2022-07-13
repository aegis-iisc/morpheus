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

let isIndented i =  
        Elet (Evar "u", (apply "getState" []), 
                Elet (Evar "b", apply "greaterint" [Evar "u", Evar "i"]),
            Eite (b, 
              Eret (Ibool true),
              Eret (Ibool false))
        )
   

let caseexp = dostmt %1 * 0.72
              [ct <- apply "offiseString" ["case"];
              e <- offisdeExp;
              ot <- apply "offiseString" ["case"];
              alts <- offsidealts;
              Elet 
              (Evar "children", concat [[ct];[e];[ot];[alts]], %3 * 0.10 
                 Ecapp (Evar "Tree", [SLit "case"; 
                                   Eapp (Evar "indentation", [Evar "ct"]),
                                   Evar "children"]))
                 ]                         

(0.71 + 0.15 + .30) 
let offsideString s = %1 * 71
    let fstpart = dostmt [assign "p" (apply "getPosition", []);
                          assign "x" (apply "sourceColumn", [Evar "p"])
                         ] in 
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]),  %1 * 0.15
                    Eite (Evar "check",
                            (apply "string" [Evar "s"] >>= 
                                    Elam (Evar "y", 
                                        Ecapp (Evar "Tree", %3 * 0.10
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
let offsideExp = %1 * 0.76
    offside_identifier <|> offside_number

same as offside_string 
(0.71 + 0.15 + .30) 
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


same as offside string 
(0.71 + 0.15 + .30) 
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


vc = 2 
let aligned_alts = %1
    let fstpart = dostmt [assign "p"  (apply "getPosition", []);
                          assign "x"  (apply "sourceColumn", [Evar "p"])] in 
    
    let sndpart = 
                Elet (Evar "check", 
                    (apply "isIndented" [Evar "x"]), %1 * 0.15
                    Eite (Evar "check",
                            many1 offside_alt, %2 * 0.71
                            (*Else *)
                            Eret (Eparser Bot)


                        )
                    ) 
      in 
      fstpart sndpart                            


