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
              (Evar "children", concat [[ct];[e];[ot];[alts]],  
                 Ecapp (Evar "Tree", [SLit "case"; 
                                   Eapp (Evar "indentation", [Evar "ct"]),
                                   Evar "children"]))
                 ]                         

 
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
let offsideExp = 
    offside_identifier <|> offside_number

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


