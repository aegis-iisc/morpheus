

predicate wellformed c = (ilssel (h, inp) = l => (fst (v) == hd (l))) /\ 	
			    ((snd (v) = con) =>  (len (con) == fst (v) -- 1))
        

predicate wellformedList [] = true
         wellformedList (x :: xs) = wellformed (v) = true /\  wellformedList (xs) = true;


typespec : State {\(h:heap). true} 
    v : { v : char |  true} 
	{\(h : heap), (v : char), (h' : heap). 
            \(x3 : string).
            ([x3='A'] \/ [x3 = 'B'])};

manychunk : State  {\(h : heap). true}
            v : {v : [pair]| true} 
		  {\(h : heap), (v : [pair]), (h' : heap). 
			wellformedList  (v) = true
          };


chunk :  State  {\(h : heap). true}
            v : {v : pair | true} 
		{\(h : heap), (v : pair), (h' : heap). 
			(ilssel (h, inp) = l => (fst (v) == hd (l))) /\ 	
			((snd (v) = con) =>  (len (con) == fst (v) -- 1))
            }; 


png : State  {\(h : heap). true}
            v : {v : png| true} 
		  {\(h : heap), (v : png), (h' : heap). 
			wellformedList  (body (v)) = true
          };

