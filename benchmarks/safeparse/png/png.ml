open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 



type png = Png {header : char list
                ; body : chunk list}

type pair = Pair of (int * char list)


let len = number 


let content len = %1 * 0.71
        do 
          res <- count len alphabet 2* 0.63
          return res



let typespec = Char "A" <|> Char "B" 



let chunk = %1 * 0.87
        do 
            len <- len 
            ts <- typespec
            let len' = len - 1 in 
            con <- content (len') 1* 0.14
            let p = Pair (len, con) in 2* 0.11
            return p



let png =  do %1 * 0.83
           h <- header 
           ts <- typespec 
           chs <- many chunk 2 * 0.62 
           let res = Png {header = h; body = chs} in 2* 0.13 
           return res