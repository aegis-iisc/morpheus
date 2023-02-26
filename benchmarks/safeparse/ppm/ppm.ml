open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 

exception CompilerExc of string 

(* ppm -> "P" versionnumber . header . body 
   versionnumber -> digit 
   header -> width . height . max 
   body  -> count height row 
   row -> count width rgb 
   rgb -> digitlt (max) . digitlt max . digitlt max *)
type triple = Triple of int * int * int 

let rgb = RGB of int * int * int

let vnumber = digit 

let header = number >>= (Elam [Evar "w"], 
                         (number >>= Elam ([Evar "h"], 
                          number >>= Elam ([Evar "m"], 
                            Ecapp (Evar "Triple", [Evar "w"; Evar "h", Evar "m"] 
                            ))) ))


let vnumber = digit 

let header = do       
      w <- number 
      h <- number 
      m <- number 
      let res = Triple (w, h, m) in  
      return res

(* *)
let rgb n = 
      do 
        r <- number_lt n 
        g <- number_lt n 
        b <- number_lt n
        let res =  RGB (r, g, b) in 
       return res


let columns tr = 
       let m = pi 3 (tr) in 
       let w = pi 1  (tr) in 
       let res = count w (rgb m) in  
       return res
      


let body tr = 
      do 
      rows <- count h (columns tr) 
      retrun rows


let ppm = 
         do 
         string "P" 
         vn <- versionnumber
         triple <- header 
         b <- body triple 
         let res = Pair (triple, b) in 
         return res 


