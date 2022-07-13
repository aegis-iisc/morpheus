open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 
open Lib
exception CompilerExc of string 


type dtriple = Triple of int * int * int 


(* 
skipfields : 
    State  {\(h : heap). true} 
	unit 
	{\(h : heap), (v : unit), (h' : heap). 
            ilssel (h, inp) = l1 /\
            ilssel (h', inp) = l2 /\
            elems (v) C= elems (l1) };   *)

let skipfields = 
            _ <- many (alphapheb)
            _ <- string ","
            _ <- ws 
            return ()


(* 
csv_row : State  {\(h : heap). true} 
                v : {v : triple} 
            {\(h : heap), (v : triple), 
                    (h' : heap). 
                    pr1 (v) >= pr2(v) 
                    pr3 (v) >= pr1 (1)};
   
  *)

let csv_row = 
        _ <- count 4 skipfields
        deaths <- number
        _ <- count 2 skipfields
        deathsmin <- number
        if (deathsmin > deaths) then 
            fail
        else
           deathsmax <- number 
           if (deaths > deathsmax) then 
                fail
           else 
            return Triple (deaths, deathsmin, deathsmax)





