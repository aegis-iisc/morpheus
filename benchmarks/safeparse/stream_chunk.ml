open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 
open Lib
exception CompilerExc of string 

type istream = {inp : [int];
               offset : int}


type tagentry = {sig : int;
                 offset : int;
                 size : int}

type icc = {tag : tagentry}

let rec droplist n l =
   if n == 0 then l 
   else 
    (drop (n-1) (match l with x::xs -> xs));;


let rec takelist n l =
   
   if n == 0 then [] 
   else
    match l with 
    | [] -> fail 
    | x::xs ->  x :: (take (n-1) (xs))


let stream = ref istream 

let tag choice = number
        
let get_stream = !stream 


let tagentry = 
    sig <- number
    offset <- number
    size <- number
    return {sig=sig; offset=offset; size=size}

(* 
take : (n : int) -> (str : istream) ->  
        -> State {\(h:heap). true} 
			istream 
		{\(h : heap), (v: istream), (h' : heap). 
		 offset (v) =  0 
         inp (v) = inp /\
         len (inp) = n}; 
    *)


let take (n : int) (str : stream) = 
        let inp = inp (str) in 
        if (n <= length inp) then 
            let inp' = take n inp in 
            {inp = inp'; offset = 0}

(* 
drop : (n : int) -> (str : istream) ->  
        -> State {\(h:heap). true} 
			istream 
		{\(h : heap), (v: istream), (h' : heap). 
		inp (str) = inp (v) /\
        offset (v) = offset  (str) + n /\
         len (inp) = n} 
    *)

let drop n str = 
    let inp = inp (str) in 
        if (n <= length inp) then 
            let offset = offset str in 
            let offset' = offset + n in 
            {inp = inp; offset = offset'}



let set_stream str = 
        steam := str

(* 
chunk : (te : tagentry) -> 
        State  {\(h : heap). true} 
		(v : unit) 
		{\(h : heap), (v : unit), (h' : heap). 
                       
                plssel (h', stream) = str' 
				/\ plssel (h, stream) = str 
				/\ plen (str') = plen (str) -- sz}; *)



let chunk te = 
        let sz = size (te) in
        let  sig = signature (te) in 
        str  <- get_stream 
        block <- take sz str 
        _ <- set_stream block 
        tag <-  tag sig
        block2 <- drop sz str
        _ <- set_stream block2
        



let icc = 
    tentry <- tagentry 
    _ <- chunk tentry 
    