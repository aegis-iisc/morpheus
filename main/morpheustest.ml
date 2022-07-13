open SpecLang
module Lambda = Lambdasyn


 
let () = 

    (*digit :: Parser <{\x -> true}, {\w1 x w2 -> subsetInput w2 w1 }> Int @-}
        digit :: Parser Int 
        digit = return 9
    number :: Praser Int 
    number = 
    *)

    let int9 = Lambda.ILit 9 in 
    let digit = Lambda.Ret  (Lambda.Eval int9) in
    let number = Lambda.Bind (digit, 
         Lambda.Elam ([Lambda.Evar (Var.fromString "x")], 
         Lambda.Eparser (
                Lambda.Ret (Lambda.Evar (Var.fromString "c"))  ))
        )    in 
         () 
        
  
