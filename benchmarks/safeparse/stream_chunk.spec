
type istream = {inp : [int];
               offset : int}


type tagentry = {sig : int;
                 offset : int;
                 size : int}

type icc = {tag : tagentry}


take : (n : int) -> (str : istream) ->  
        -> State {\(h:heap). true} 
			istream 
		{\(h : heap), (v: istream), (h' : heap). 
		 offset (v) =  0 
         inp (v) = inp /\
         len (inp) = n}; 


drop : (n : int) -> (str : istream) ->  
        -> State {\(h:heap). true} 
			istream 
		{\(h : heap), (v: istream), (h' : heap). 
		inp (str) = inp (v) /\
        offset (v) = offset  (str) + n /\
         len (inp) = n} 


chunk : (te : tagentry) -> 
        State  {\(h : heap). true} 
		(v : unit) 
		{\(h : heap), (v : unit), (h' : heap). 
                       
                plssel (h', stream) = str' 
				/\ plssel (h, stream) = str 
				/\ plen (str') = plen (str) -- sz}; 
