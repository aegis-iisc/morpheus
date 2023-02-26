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
type expression = Address of expression | Bitwise of (expression * expression) | 
                    Cast of string * expression 
                    | Identifier of Sstring 





typeexp = 
    string "bool" 
    <|>
    string "int"     

typedecl = 
        do 
        td <- keyword "typedef" 
        te <- typeexp
        id <- indentifier 
        let b = memberId id 
        if (!b) then                                   
            _ <- addType id 
            Tdecl {typeexp; id}
        else 
            fail  

typename = 
        do 
        x <- identifier 
        let b = memberTypes x 
        if (b) then 
            return x
        else 
            fail    

externvardecl = 
        do 
        td <- keyword "extern" 
        te <- typeexp
        id <- indentifier 
        let b = memberTypes id 
        if (!b) then                                   
            _ <- addIdentifiers id 
             Evar {typeexp; id} 
        else 
            fail  
(* expr = 
    & expresion 
    | (typename)
    | identifierexp *)  




expression =
            do 
            string "amp"  
            i <- identifier 
            return Address i
            <|> 
            do string "(" 
            tn <- typename 
            string ")" 0.11
            e <- expression
            return Cast (tn, e))
            <|> 
            do 
            i <- dentifier
            let b = memberTypes i 
            if (!b) then                                   
            _ <- addIdentifiers id 
              return  Identifier {i} 
            else 
                fail

