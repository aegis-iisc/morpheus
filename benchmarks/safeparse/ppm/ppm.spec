
type triple = Triple of {width  :int;
                        height : int;
                        max : int };

type numberlt n = {v : int | v <= n};

type rgb m = RGB of (numberlt m) * (numberlt m) * (numberlt m)  
type row w m = {v : [(rgb m)]  | len v = w}  
type ppmdata = {head : triple; 
                data : {v : [[row]] | len v = snd (head)}}


header : State {\(h : heap).true} 
        triple 
	   {\(h:heap),(v:triple),(h':heap). included (h',h, inp) = true};



rgb : ({n : int | true})  -> {v : rgb n | true};



columns : ({tr : triple | true}) -> {v : [rgb] | len (v) = width (tr)};


body : ({tr : triple | true}) -> 
        {\(h : heap). true} 
            [[rgb]] 
            {\(h:heap),(v:[[rgb]]),(h':heap). len (v) ==  height (tr)};



ppm : State {\(h : heap).
				true
                }
                v : {v : ppmdata  | true}
                 {\(h : heap), (v : typeexpr), (h' : heap).
                   included (h', h, inp) = true
                };    


