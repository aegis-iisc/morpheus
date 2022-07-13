type tree = Tree {term : string;
                    indentT : int; 
                    children : [tree]};


cons : (x : { v : tree | offsideTree (v) = true}) -> (xs : {v : [tree] | offsideTreeList (v) = true}) -> 
                    {v : [tree] | len (v) = len (xs) + 1 /\
                                offsideTreeList (v) = true};

CErr : char_err;
Err : err;


doBlock : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int), (Inp ).
            (sel (h, ist) = I /\   
            sel (h', ist) = I' /\ 
            sel (h, inp) = Inp) =>   
            
            (offsideTree (I, v) = true /\ 
            I' = I /\ 
            sel h' inp C= sel h inp)
            } 


do_ : State {\(h : heap). true} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
             sel h' inp C= sel h inp)
            }; 


indented_reserved : ({s : string | true }-> State {sel (h, ist) = I}
                                    v : { v : tree |  true} 
                                    {\(h : heap), (v : tree), (h' : heap).
                                    offsideTree (I, v) = true /\
                                    sel (h, ist) = sel (h’, ist) /\
                                    indentT (v) = pos (sel (h, inp) /\
                                    included (h’,h, inp) /\
                                    sel h' inp C= sel h inp)};
                

indentedDo  : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I} 
             v : { v : tree |  true} 
	        {\(h : heap), (v : tree), (h' : heap).
              \(I : int), (I' : int).
            (sel (h, ist) = I /\   
            sel (h', ist) = I') =>   
            (offsideTree (I, v) = true /\ 
            sel h' inp C= sel h inp)
            };

indentedDoBlock : State {\(h : heap). 
                \(I : int).
                sel (h, ist) = I}
              v : { v : tree list |  true} 
            {\(h : heap), (v : tree), (h' : heap).
             offsideTreeList (I, v) = true /\
            sel (h, ist) = sel (h’, ist) /\
            included (h’,h, inp)};


indent : State State {\(h : heap). true}
                  v : { v : tree |  true} 
            {\(h : heap), (v : tree), (h' : heap).
             h' = h};
