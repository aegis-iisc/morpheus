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

let header = do %1 * 0.71
      w <- number 
      h <- number 
      m <- number 
      let res = Triple (w, h, m) in  3* 0.13
      return res

(* *)
let rgb n = %1 * 0.83
      do 
        r <- number_lt n 
        g <- number_lt n 
        b <- number_lt n
        let res =  RGB (r, g, b) in 3* 0.13 
       return res


let columns tr = %1 * 0.72
       let m = pi 3 (tr) in %1 * 0.11
       let w = pi 1  (t3) in %1 * 0.13
       let res = count w (rgb m) in  %2 * 0.56
       return res
      


let body tr = %1 0.92
      do 
      rows <- count h (columns tr) 2% 0.67
      retrun rows


let ppm = %1 * 0.87
         do 
         string "P" %1 * 0.11
         vn <- versionnumber
         triple <- header 
         b <- body triple % 1* 0.15
         let res = Pair (triple, b) in %2 * 0.11
         return res 


