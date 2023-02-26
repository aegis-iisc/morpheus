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


let content l = 
        do 
          res <- count l alphabet 
          return res



let typespec = Char "A" <|> Char "B" 



let chunk = 
        do 
            len <- len 
            ts <- typespec
            let len' = len - 1 in 
            con <- content (len') 
            let p = Pair (len, con) in 
            return p



let png =  do 
           h <- header 
           ts <- typespec 
           chs <- many chunk 
           let res = Png {header = h; 
                        body = chs} in  
           return res