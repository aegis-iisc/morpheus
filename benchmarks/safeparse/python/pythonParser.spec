type tree = Tree {term : string;
                  indentT : int; 
                    children : [tree]};



type offsideTree i = 
                  Tree {term : string;
                        indentT : { v : int | v > i}; 
                        children : [offsideTree i]};


predicate offsideTree i t = indentT (t) > i /\ offdiseTreeList (children (v)) = true
predicate offsideTreeList [] = true 
            offsideTreeList x :: xs = offsideTree x /\ offsideTreeList xs
 

type pos = {line : int; col : int}
type input = (pos * char) list 
inp : input ref 

ist : int ref 



nil : { v : [tree] | len (v) = 0};
cons : (x : { v : tree | offsideTree (v) = true}) -> (xs : {v : [tree] | offsideTreeList (v) = true}) -> 
                    {v : [tree] | len (v) = len (xs) + 1 /\
                                offsideTreeList (v) = true};


CErr : char_err;
Err : err;

 t_while :  State { top (brace_ist (sel h ist)) = I } 
               v :  {v : tree | true } 
            {\(h : heap), (v : tree), (h' : heap).
                \(I : int), (I' : int).
             (sel (h, ist) = I /\ sel (h', ist) = I') =>
             offsideTree (v, I) = true /\
             I' > I /\   
             sel h' inp C= sel h inp}; 

suite :  State {\(h: heap). sel (h, ist) = I } 
               v :  {v : tree | true } 
            {\(h : heap), (v : tree), (h' : heap).
                \(I : int), (I' : int).
             (sel (h, ist) = I /\ sel (h', ist) = I') =>
             offsideTree (v, I) = true /\
             I' > I /\   
             sel h' inp C= sel h inp}; 

t_exp : State {\(h: heap). sel (h, ist) = I } 
               v :  {v : tree | true } 
            {\(h : heap), (v : tree), (h' : heap).
            \(I : int), (I' : int).
             (sel (h, ist) = I /\ sel (h', ist) = I') =>
             offsideTree (v, I) = true /\
             sel h' inp C= sel h inp}; 
 


t_stmts :  State  {\(h : heap). sel (h, ind) == I} 
		v : { v : [tree] | true  } 
		{\(h : heap), (v : [tree]), (h' : heap). 
            offsideTreeList (I, v) = true};

offside_string : ({ s : string | true} ) -> 
           State  {\(h : heap). sel (h, ind) == I} 
		    v : { v : tree | true } 
		{   \(h : heap), (v : tree), (h' : heap). 
            offsideTree (I, v) = true};
     