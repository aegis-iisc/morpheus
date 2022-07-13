

type list = Nil 
    | Cons of int * list; 


inp : [char];
x : char;
y : char;
z: char;
nil : { v : [char_result] | len (v) = 0};
cons : (x : { v : char_result | true}) -> (xs : {v : [char_result] | true}) -> {v : [char_result] | len (v) = len (xs) + 1};

subsone :  (n : { v : int | true}) -> {v : int | v = n - 1 }; 
int_of_string : (xs : {v : [string] | true}) -> {v : int | true};


CErr : char_err;

Err : err;
t_val : {v : int | [v = 9]};
t_match : {v : int | [v = 9]};

t_lam : (x : { v : char | true}) -> {v : int | [v = 9]};


t_app : {v : int | [v = 9]};

t_ret : State {\(h:heap). true} 
    v : { v : char |  true} 
	{\(h : heap), (v : char), (h' : heap). [h' = h]};


t_bind : State {\(h:heap). true} 
    v : { v : int |  true} 
	{\(h : heap), (v : int), (h' : heap). [h' = h] /\ [v=9]};

eps : State {\(h:heap). true} 
    v : { v : unit |  true} 
	{\(h : heap), (v : unit), (h' : heap). [h' = h]};


cparsera : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap).
            \(x2 : string).
            (v = Inlchar (x2) => [x2 = 'a'] /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};


cparserb : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap).
            \(x2 : string).
            (v = Inlchar (x2) => [x2 = 'b'] /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};

altab : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap). 
            \(x3 : string).
            (v = Inlchar (x3) => ([x3 = 'b'] \/ [x3 = 'a'])
                    /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};


bot : Exc {\(h:heap). true} 
    v : { v : result |  true} 
	{\(h : heap), (v : result), (h' : heap). 
            v = Inr (Err) /\  [h' = h]};








t_lamb : (x : { v : char | true}) -> 
    StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap). 
            (v = Inlchar (x1) => [x1 = 'b'] /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};



onetwothree : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap). 
            \(x3 : string).
            (v = Inlchar (x3) => ([x3 = '1'] \/ [x3 = '2'] \/ [x3 = '3'] )
                    /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};




digit : StExc {\(h:heap). true} 
    v : { v : char_result |  true} 
	{\(h : heap), (v : char_result), (h' : heap). 
            \(x3 : string).
            (v = Inlchar (x3) => ([x3='0'] \/ [x3 = '1'] \/ [x3 = '2'] \/ [x3 = '3']
                                   \/ [x3 = '4'] \/ [x3 = '5'] \/ [x3 = '6'] 
                                   \/ [x3 = '7'] \/ [x3 = '8'] \/ [x3 = '9'] )
                    /\ includes (h', h, inp) = true) /\
            (v = Inrchar (CErr) => includes (h', h, inp) = true)};

x : char_result;
xs : [char_result]; 


pstar : State {\(h:heap). true} 
            v : { v : [unit] |  true} 
	{\(h : heap), (v : [unit]), (h' : heap). 
             includes (h', h, inp) = true};


startest : State {\(h:heap). true} 
            v : { v : [unit] |  true} 
	{\(h : heap), (v : [unit]), (h' : heap). 
             includes (h', h, inp) = true};


four : {v : int | v = 4};

countnp : (n : {v : int | true}) -> State {\(h:heap). true} 
                               v : { v : [unit] |  true} 
	                        {\(h : heap), (v : [unit]), (h' : heap). 
                             len (v) = n 
                            /\  includes (h', h, inp) = true};


counttest : State {\(h:heap). true} 
            v : { v : [unit] |  true} 
	{\(h : heap), (v : [unit]), (h' : heap). 
             len (v) = 4 
           /\  includes (h', h, inp) = true};


pstar : State {\(h:heap). true} 
            v : { v : [char_result] |  true} 
	{\(h : heap), (v : [char_result]), (h' : heap). 
             includes (h', h, inp) = true};

number : State {\(h:heap). true} 
            v : { v : [char_result] |  true} 
	{\(h : heap), (v : [char_result]), (h' : heap). 
             includes (h', h, inp) = true};


len : State {\(h:heap). true} 
            v : { v : int |  true} 
	{\(h : heap), (v : int), (h' : heap). 
             includes (h', h, inp) = true};


content : (y : {v : int | true}) -> 
        State {\(h:heap). true} 
            v : { v : [char_result] |  true} 
	{\(h : heap), (v : [char_result]), (h' : heap). 
             len (v) = y /\
             includes (h', h, inp) = true};



createPair : (y : {v : int | true}) -> (ys : { v : [char_result] |  true}) -> 
                                            {v : int_char_resultP | len (snd_icp(v)) = fst_icp (v)};