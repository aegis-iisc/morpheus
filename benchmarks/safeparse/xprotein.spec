type header = Header of int
type protein = {head : header;
                id : int; pname : [char]}; 

puids : ref [int];
pnames : ref [string];


header : State  
    {\(h : heap). Ilssel (h, pnames) = Pin => 
                    uintlist (p) = true  } 
	header 
	{\(h : heap), (v : protein), (h' : heap). 
		ilssel (h, inp) = l0 /\ 
        ilssel (h', inp) = l1 /\ 
        elems (l1) C= elems (l0)
		/\ Ilssel (h', puids) = Pout
		/\ contains (Pout, v) = true /\
        uintlist (Pout) = true};

protein : State  
    {\(h : heap). Ilssel (h, pnames) = Pin => 
                    ustringlist (pnames) = true  } 
	protein 
	{\(h : heap), (v : protein), (h' : heap). 
		ilssel (h, inp) = l0 /\ 
        ilssel (h', inp) = l1 /\ 
        elems (l1) C= elems (l0)
		/\ Ilssel (h', pnames) = Pout
		/\ Ielems (Pout) = Ielems (Pin) U {pname (v)} 
		/\ contains (Pout, v) = true /\
        ustringlist (Pout) = true};        