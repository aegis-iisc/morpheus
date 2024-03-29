typeexp : State {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty) =>  
                    ldisjoint (Id, Ty) = true
                }
                    v : {v : typeexpr  | true}
                 {\(h : heap), (v : typeexpr), (h' : heap).
                    \(Id : [string]), (Ty : [string]), (Id' : [string]), (Ty' : [string]).
                    idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty'/\
                    ldisjoint (Id', Ty') = true
                    
                };    


identifier : State {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty) =>  
                    ldisjoint (Id, Ty) = true
                }
                   v : { v : string | true}
                {\(h : heap), (v : string), (h' : heap).
                    \(Id : [string]), (Ty : [string]), (Id' : [string]), (Ty' : [string]).
                    idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty'/\
                    ldisjoint (Id', Ty') = true
                    
                };
             

 
memberId : (x : {v  : string | true}) -> 
                State {\(h:heap). true}
                    v : { v : bool | true} 
				{\(h: heap),(v : bool),(h': heap).
                    \(Id : [string]), (Id' : [string]).
                        idsel (h', ids) = Id' /\
                        idsel (h, ids) = Id /\
                        tysel (h, types) = tysel (h', types) /\
                        Id' = Id /\
                        ([v = true] <=> memids (Id', x) = true) /\
						([v = false] <=> memids (Id', x) = false)
                        }; 




memberTypes : (x : {v  : string | true}) -> 
                State {\(h:heap). true}
                    v : { v : bool | true} 
				{\(h: heap),(v : bool),(h': heap).
                    \(Ty : [string]), (Ty' : [string]).
                    idsel (h', ids) =  idsel (h, ids) /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty'/\
                    Ty' = Ty /\
                    ([v = true] <=> memtypes (Ty', x) = true) /\
					([v = false] <=> memtypes (Ty', x) = false)
                    }; 





addId : (s : {v : string | true}) -> 
                 State {\(h : heap).
				\(Id : [string]).
                   (idsel (h, ids) = Id => 
                    memids (Id, s) = false)
                }
                    v : {v : unit | true}
                {\(h : heap), (v : unit), (h' : heap).
                    \(Id : [string]),(Id' : [string]).
                    idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = tysel (h', types)/\
                    memids (Id', s) = true /\
				    slsize (Id') == slsize (Id) + 1
				 };    





addType : (s : {v : string | true}) -> 
                 State {\(h : heap).
				\(Ty : [string]).
                    (tysel (h, types) = Ty =>  
                    memtypes (Ty, s) = false)
                }
                    v : { v : unit | true}
                {\(h : heap), (v : unit), (h' : heap).
                    \(Ty : [string]),(Ty' : [string]).
                    idsel (h', ids) = idsel (h, ids) /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty'/\
                    memtypes (Ty', s) = true /\
				   slsize (Ty') ==slsize (Ty) + 1
				 };    

externvardecl : State {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\  
                    ldisjoint (Id, Ty) = true)
                }
                v : {v : externvar | true}		
	 	 	    {   \(h : heap), (v : externvar), (h' : heap).
                    \(Id : [string]), (Ty : [string]), (Id' : [string]), (Ty' : [string]).
                    (idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty') => 
                 

	 	 	    	(ldisjoint (Id', Ty') = true)
	 	 	     				};
typedecl : Exc {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\  
                    ldisjoint (Id, Ty) = true)
                }
                v : {v : tdecl result | true}		
	 	 	    {   \(h : heap), (v : typeexpr), (h' : heap).
                    \(Id : [string]), (Ty : [string]), (Id' : [string]), (Ty' : [string]).
                    v = Inl (v1) => 
                    (idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty') => 
                 

	 	 	    	(ldisjoint (Id', Ty') = true)
                    /\
                    v = Inr (Err) => (included(inp,h,h') = true   

	 	 	    };

expression : State {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\  
                    ldisjoint (Id, Ty) = true)
                }
                v : {v : expression | true}		
	 	 	    {   \(h : heap), (v : typeexpr), (h' : heap).
                    \(Id : [string]), (Ty : [string]), (Id' : [string]), (Ty' : [string]).
                    (idsel (h', ids) = Id' /\
                    idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\
                    tysel (h', types) = Ty') => 
     	 	    	(ldisjoint (Id', Ty') = true)
				};

typename : Stexc {\(h : heap).
				\(Id : [string]), (Ty : [string]).
                   (idsel (h, ids) = Id /\
                    tysel (h, types) = Ty /\  
                    ldisjoint (Id, Ty) = true)
                }             
                v : {v : string | true}		
	 	 	    {   \(h : heap), (v : typeexpr), (h' : heap).
                    \(Id' : [string]), (Ty' : [string]).
                    (idsel (h', ids) = Id' /\
                    tysel (h, types) = Ty' =>
                    (ldisjoint (Id', Ty') = true /\
                    mem (Ty', v) = true)
				};