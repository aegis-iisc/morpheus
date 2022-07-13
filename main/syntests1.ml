open SpecLang
module Lambda = Lambdasyn




let int9 = Lambda.ILit 9  
let digit = Lambda.Ret  (Lambda.Eval int9)
let int_of_char = Lambda.ELam ()        
let number : Lambda.monExp = 
    Lambda.Eparser 
        (Lambda.Bind (digit, 
         Lambda.Elam ([Lambda.Evar (Var.fromString "x")], 
         Lambda.Eparser (
                Lambda.Ret (Lambda.Evar (Var.fromString "c"))  ))
        ))   
        
  
