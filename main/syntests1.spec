digit : StExc {\(h : heap). true} v : char 
       {\(h : heap), (v : char), (h' : heap). 
        v = '9' && 
        sel (h', inp) C= sel (h, inp)
        } 
		
        
number : StExc {\(h : heap). true} v : int 
       {\(h : heap), (v : char), (h' : heap). 
        sel (h', inp) C= sel (h, inp)
        }