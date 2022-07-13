open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 
open Lib
exception CompilerExc of string 

type header = Header of int
type protein = {head : header;
                id : int; pname : [char]} 
let puids = ref []
let pnames = ref []

(*
header : State  
    {\(h : heap). Ilssel (h, pnames) = Pin => 
                    uintlist (p) = true  } 
	header 
	{\(h : heap), (v : protein), (h' : heap). 
		ilssel (h, inp) = l0 /\ 
        ilssel (h', inp) = l1 /\ 
        elems (l1) C= elems (l0)
		/\ Ilssel (h', puids) = Pout
		/\ contains (Pout, v) = true /\
        uintlist (Pout) = true}; *)

let header = 
    _ <- string "<header>"
    uid <- number
    name <- identifier 
    _ <- close "<\header>"
    
    if (contains puids uid) then 
        fail
    else  
        puids :=  (uid :: !uids)     
        return Header uid

(* protein : State  
    {\(h : heap). Ilssel (h, pnames) = Pin => 
                    ustringlist (pnames) = true  } 
	protein 
	{\(h : heap), (v : protein), (h' : heap). 
		ilssel (h, inp) = l0 /\ 
        ilssel (h', inp) = l1 /\ 
        elems (l1) C= elems (l0)
		/\ Ilssel (h', pnames) = Pout
		/\ Ielems (Pout) = Ielems (Pin) U {pname (v)} 
		/\ contains (Pout, v) = true /\
        ustringlist (Pout) = true}; *)

let protein = 
    head <- header
    _ <- string "<protein>"
    name <- identifier 
    uid <- uid
    
    _ <- close "<\protein>"
    
    if (contains pnames name) then 
        fail
    else  
        pnames :=  (name :: !pnames)     
        return {head = head; id = uid; pname = name}