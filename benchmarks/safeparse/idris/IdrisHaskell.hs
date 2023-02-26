module IdrisParser where 

-- import Parsec   
data IState = IState {
     ist :: Int
     
} deriving (Show)

-- High level language terms
data PTerm =  PDoBlock [PDo]                               
	     
data PDo t =  DoExp   t
            | DoExt t 
            | DoLet  t t  
            
type IdrisParser a = Parser IState a 

getIst :: IdrisParser IState
getIst = get 

putIst :: IdrisParser ()
putIst i = put {ist = i}

doBlock :: IdrisParser PTerm
doBlock = do  
            reserved "do"
            ds <- indentedDoBlock
            return (PDoBlock ds)

indentedDo ::  IdrisParser PDo
indentedDo = do 
                allowed <- ist getIst 
                i <- indent
                if (i < allowed ) 
                   then fail ("end of block")
                else do_ 


do_ :: IdrisParser PDo 
do_  =  do 
         reserved "let"
         i <- name
         reservedOp "="
         e <- expr 
         return (DoLet i e)
   <|>  do 
         i <- extension
         e <- expr ;
         return (DoExt  i e)
   <|>  do e <- expr 
           return (DoExp  e)
   

indentedDoBlock :: IdrisParser [PDo]
indentedDoBlock  = do 
                    allowed <- ist getIst   
                    lvl' <- indent 
                    if (lvl' > allowed) then 
                        do 
                            putIst lvl' 
                            res <- many (indentedDo) 
                            putIst allowed 
                            return res 
                     else 
                        fail "Indentation error"

indent :: IdrisParser Int                     
indent =    do    
                  inp <- getInput
                  next <- lookAheadMatches (reservedOp)  
                  if (next) then 
                       do 
                         lexeme 
                         return (P.unPos . P.sourceColumn $ P.getSourcePos)
                  else 
                         return (P.unPos . P.sourceColumn $ P.getSourcePos)

lookAheadMatches :: IdrisParser a -> IdrisParser Bool 
lookAheadMatches p = do match <- lookAhead (optional p)
                        return $ isJust match
 