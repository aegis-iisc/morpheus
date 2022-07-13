(* decl := typedef . typeexpr . id=rawident [¬ id ∈ (!identifiers)]
{types.add id}
| ...
typename := x = rawident [x ∈ (!types)]{return x}
typeexp := "int" | "bool"
expr := .... | id=rawident {identifiers.add id ; return id} *)

open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 

val identifiers : (string list) ref 
val types : (string list) ref 

let identifiers = ref []
let types = ref []

type decl = Typedecl of tdecl
          | ExternVar of externvar
        
type typeexp =  TEint of int | TEbool of bool 

type tdecl = Tdecl of {typexp : typeexp; tname : string}
type externvar = Evar of {typexp : typeexp; vname : string}






typeexp = 0.68
    string "bool" 0.11
    <|>
    string "int" 0.11
    

typedecl = %1 * 0.92
        do 
        td <- keyword "typedef" %1 * 0.11
        te <- typeexp
        id <- indentifier 
        let b = memberId id %1 * 0.15
        if (!b) then                                   
            _ <- addType id % 1 * 0.11
            Tdecl {typeexp; id} %2 * 0.12
        else 
            fail  

typename = %1 0.82 
        do 
        x <- identifier 
        let b = memberTypes x %1 * 0.11 
        if (b) then 
            return x
        else 
            fail    

externvardecl = %1 0.82
        do 
        td <- keyword "extern" %1 0.11
        te <- typeexp
        id <- indentifier 
        let b = memberTypes id %1 0.15
        if (!b) then                                   
            _ <- addIdentifiers id %1 0.11
             Evar {typeexp; id} %2 0.11
        else 
            fail  
(* expr = 
    & expresion 
    | (typename)
    | identifierexp *)  




expression = (string "amp" i %1 * 0.92 + %1 * 0.11
            i <- identifier 
            return i  )
            <|> 
            (string "(" %1 * 0.11
            tn <- typename 
            string ")" 0.11
            return tn)
            <|> i <- dentifier
                retrun i


