

type list = Nil 
    | Cons of int * list; 



x : { v : int | [v=9]};
z : int;

t_val : {v : int | [v = 9]};
t_match : {v : int | [v=9]};
t_lam : (x : { v : int | true}) -> {v : int | [v = 9]};


t_app : {v : int | [v = 9]};

t_ret : State {\(h:heap). true} 
    v : { v : char |  true} 
	{\(h : heap), (v : char), (h' : heap). [h' = h]};


t_bind : State {\(h:heap). true} 
    v : { v : int |  true} 
	{\(h : heap), (v : int), (h' : heap). [v=9]};
