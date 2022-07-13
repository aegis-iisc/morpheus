

type dtriple = Triple of int * int * int 

skipfields : 
    State  {\(h : heap). true} 
	unit 
	{\(h : heap), (v : unit), (h' : heap). 
            ilssel (h, inp) = l1 /\
            ilssel (h', inp) = l2 /\
            elems (v) C= elems (l1) };



csv_row : State  {\(h : heap). true} 
                v : {v : triple} 
            {\(h : heap), (v : triple), 
                    (h' : heap). 
                    pr1 (v) >= pr2(v) 
                    pr3 (v) >= pr1 (1)};


