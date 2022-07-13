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


let bidderinfo s = %1 
      do 
      _ <- string "<bidderinfo>" 1* 0.12
      bn <- biddername
      br <- bidderrating 
      _ <- string "</bidderinfo>" %1 * 0.15
      if (bn = s) then 
            fail 
      else 
           return Bidder {name = bn; rating = br} 2* 0.13


let auctioninfo s = many (bidderinfo s) 2 * 0.79 + 1 * 0.15

let listing  = %1 * 0.92
      do 
      _ <- string "<listing>" %1 * 0.12
      si <- sellerinfo 
      ais <- autioninfo si %1 * 0.82
      _ <- string "</listing>" %1 * 0.11
      let res = Listing {seller = si; bidders= ais}  in 2* 0.15
      return res


