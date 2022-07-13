
sellerinfo :
        State  {\(h : heap). true} 
		 v :{v : sellerinfo | true}
		{\(h : heap), (v : sellerinfo), (h' : heap). included(h', h, inp) = true};


bidderinfo : ({s : [char] | true}) ->  
        State {\(h : heap). true} 
		    v  : {v : bidder | true}
		{\(h : heap), (v : bidder), (h' : heap). 
        not (name (bidder) == s) };







listing : State {\(h : heap). true} 
    v : {v : listing | true}
{\(h : heap), (v : bidder), (h' : heap). 
     seller (v) = si /\ 
    bidders (v) = bis /\ disjoint_sellerbidder(si, bis) = true
   /\ included (h', h, inp) = true};

