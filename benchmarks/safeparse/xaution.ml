open Lambdasyn
open SpecLang
module SEL = SpecElab
module STC = Syntypechecker
module R = Rparsec
module Gamma = Environment.TypingEnv 
open Lib
exception CompilerExc of string 


type sellerinfo = Seller{name:[char]; rating:int}
type bidderinfo = Bidder {name:[char]; rating:int}
type listing = Listing {seller : sellerinfo; 
                        bidders : [bidderinfo]}

let sellername = identifier 
let biddername = identifier 

let sellerrating = number 
let bidderrating = number
same as bidderinfor
let sellerinfo = 
      do 
      _ <- string "<sellerinfo>"
      sn <- sellername      
      sr <- sellerrating
      _ <- string "</sellerinfo>"
      let res = Seller {name = sn; rating = sr} in 
      return res


let bidderinfo s =  
      do 
      _ <- string "<bidderinfo>" 
      bn <- biddername
      br <- bidderrating 
      _ <- string "</bidderinfo>" 
      if (bn = s) then 
            fail 
      else 
           return Bidder {name = bn; rating = br} 


let auctioninfo s = many (bidderinfo s) 

let listing  = 
      do 
      _ <- string "<listing>" 
      si <- sellerinfo 
      ais <- autioninfo si       
      _ <- string "</listing>" 
      let res = Listing {seller = si; bidders= ais}  in 
      return res


