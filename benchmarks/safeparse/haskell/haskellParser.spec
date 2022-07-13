
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


getState : 
        State{\(h:heap). true}
            v : {v : int | true} 
        {\(h : heap), (v : tree), (h' : heap).
            v = sel (h, ist)};


isIndented : (i : { v : int | true}) -> 
        State{\(h:heap). true}
            v : {v : bool | true} 
        {\(h : heap), (v : tree), (h' : heap).
             [v = true] <=> i > sel (h, ist)};



isAligned : (i : { v : int | true}) -> 
        State{\(h:heap). true}
            v : {v : bool | true} 
        {\(h : heap), (v : tree), (h' : heap).
             [v = true] <=> i = sel (h, ist)};


getPosition : State{\(h:heap). true}
            v : {v : pos | true} 
        {\(h : heap), (v : pos), (h' : heap).
            \(In : [(int * char)]). 
            sel (h, inp) = Inp => 
             fst (top (Inp)) = v};
 

sourceColumn : (p : {v : pos | true}) -> {v : int | v = col (p)};



caseexp :  State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : offsideTree I |  true} 
	        {\(h : heap), (v : offsideTree I), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            I' = I /\ 
            sel(h', inp) C= sel(h, inp))
            }; 

offsideString : (i : { v : string | true}) -> 
           State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (node (v) = s /\
            offsideTree (I, v) = true /\ 
            sel (h', inp) C= sel (h, inp)
            )
            }; 

offsideExp : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (node (v) = s /\
            offsideTree (I, v) = true /\ 
            sel h' inp C= sel h inp)
            }; 

offside_identifier : 
            State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (node (v) = s /\
            offsideTree (I, v) = true /\ 
            sel h' inp C= sel h inp)
            };

offside_number : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I
                } 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (node (v) = s /\
            offsideTree (I, v) = true /\ 
            sel h' inp C= sel h inp)
            };            

aligned_alts : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I
                } 
             v : { v : [tree] |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (node (v) = s /\
            offsideTreeList (I, v) = true /\ 
            sel h' inp C= sel h inp)
            };            
          