
type 'a tree = Tree {term : 'a; 
                     indentT : int; 
                     children : ['a tree]}


For example, consider the grammar fragment taken from the official Idris language for a {\it 
do-block} in Idris parser:
\begin{lstlisting}[escapechar=\@,basicstyle=\small\sf,breaklines=true]
 DoBlock ::= 'do' OpenBlock Do+ CloseBlock;
 Do ::=
    'let' Name  TypeSig'?      '=' Expr
  | 'let' Expr'                '=' Expr
  |  Name  '<-' Expr
  |  Expr' '<-' Expr
  |  Ext Expr
  |  Expr  
  ;
\end{lstlisting}

The Idris documentation specifies the indentation rule saying that the indentation of each do statement in 
{\sf Do+} must be greater than the current indentation from which the rule is invoked. 
For instance, consider the following Idris code fragment:
\begin{lstlisting}[escapechar=\@,basicstyle=\small\sf,breaklines=true]
 expr =  do t <- term 
	    symbol "+" 
	    e <- expr 
	    pure t + e
	  symbol '*'      
\end{lstlisting}
The last statement is not a part of the do block, while the inner three statements are. 
A correct Idris parser must ensure that such indentation rules are respected. 


(* 
Expr' ::=  "External (User-defined) Syntax"
      |   InternalExpr;


Do' ::= Do KeepTerminator;
DoBlock ::=
  'do' OpenBlock Do'+ CloseBlock;
 

 Do ::=
    'let' Name  TypeSig'?      '=' Expr
  | 'let' Expr'                '=' Expr
  |  Name  '<-' Expr
  |  Expr' '<-' Expr
  |  Ext Expr
  |  Expr  
  ;
*)

(* doBlock : PE state {∀ h. \(I : int). sel (h, ist) = I}
v : pterm offsideTree I
{∀ h, v, h'.∀ (I : int), (I' : int).
(sel (h, ist) = I ∧ sel (h', ist) = I') =>
(I' = I ∧ sel h' inp C= sel h inp)
} *)
val doBlock : pterm tree  
let doBlock 
    = do dot <- indented_reserved "do"
         ds  <- indentedDoBlock 
         Tree {term = PDoBlock ds; 
               indentT = indnetT (dot);
               children = concat [[dot];ds]}

To prove that the tree returned at 65 is an offsideTree I for the initial I, 
we need to reason that both dot and ds return an offsideTree I and [offsideTree], 
this requires a) stateful reasoning in indented_reserved proving that it satisfies the safety property 

(* s -> PE state {∀ h. \(I : int). sel (h, ist) = I}
v : offsideTree I
{∀ h, v, h'.∀ (I : int), (I' : int).
term (v) = s /\
sel h' inp C= sel h inp)
} *)
let indented_reserved s = 
        do ist <- get
           i <- indent
           if (i < ist )
                then fail ("incorrect indentation")
           else 
             let res = resrved s in 
             Tree {term = res;
                   indentT = i;
                   children =  []};
We furthher need to reason over combinator monadic-sequencing sequencing the two parsers.

In order to prove that ds is a list of offsideTree I, we need more complex reaasoning 
First we need to reason over update operations in indentedDoBloc (e.g. ist:= lvl', etc.) 
and reason about another combinator many.

In \name\ many is a derived combinator implemented using a recursive fix-point combinator, 
whose typing semantics allows us to reason about such parser.
More generally, a major challenge in verification is effectful reasoning over parser combinators, which are higher-order
functions with states and other effects. \name\ axiomatizes the semantics of 
a set of primitive combinators, and since other complex combinators are 
derived from these, their type can be automatically synthesized, there by allowing us to reason about parsers 
like many (indentedDo). 




val do_ : tree pterm
let do_ 
     = (do lt <- 
                reserved "let"
               i <- name
               reservedOp "="
               e <- expr 
               let term = DoLet i e in 
               Tree {term;indentT (lt);[lt;i;e]}
   <|>  do ude <- extension 
           e <- expr 
           let term = DoExp e in  
           Tree {term;indentT (udk);[ude;e]}
                       
   <|> do e <- expr 
          let term = DoExp e in 
          Tree {term;indentT (e);[e]}
   <|> ...


let extension = "mplus" <|> ....


let indentedDoBlock  = 
                do last <- get 
                   ist <- get
                   lvl' <- indent
                   if (lvl' > ist)
                        then 
                        do  ist := lvl'; 
                            res <- many (indentedDo)
                            ist := last;
                            return res 
                    else fail ("Indentation error")


Finally in indentedDo, we need to reason that indentedDo actually returns
an indentedTree I, baically satisfying the following specification.
(* PE state {∀ h. \(I : int). sel (h, ist) = I}
v : offsideTree I
{∀ h, v, h'.∀ (I : int), (I' : int).
 sel h' inp C= sel h inp)
}  *)
let indentedDo =   do  ist <- get
                        i <- indent
                        if (i < ist )
                            then fail ("end of block")
                        else 
                            res <- do_ 
                            assert (indentT(res) >= i);
                            return res
                            (* the problem is we are not checking that the indentation of the
                                returned tree is >= i *)     

However, note that the conditional check at line 150 is not sufficent to prove this property, 
given the weak specifciation for indnet, thus \name\ will treat this program as illtyped.
In order for this program to typecheck, each choice in the do_ must be explicitly indented checked, a solution
suggested by earlier works~\cite{}

Finally the indent function for the Parsec Library has the b
val indent : PE^{pure} {∀ h.true} 
                        {v : int | tue}
                        {h' = h}
let indent = P.unPos . P.sourceColumn <$> P.getSourcePos
