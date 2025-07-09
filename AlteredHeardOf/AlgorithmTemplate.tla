-------------------------------- MODULE AlgorithmTemplate --------------------------------
EXTENDS Naturals, FiniteSets

Init(P,V) == [P ->
                  { [x : v  , 
                     d : {} ] : v \in V } 
             ]



S(s,r) ==  CASE r = 0 -> [x |-> s.x ] \* Send value (x)

           []   r = 1 -> [x |-> s.x , \* Send value (x)     
                          d |-> s.d ] \* and  value (d)
                          
           []   r = 2 -> [x |-> {}  ] \* Send NULL ({})
           
           []   r = 3 -> {}           \* Does not send message
                    
T(s,r,M) ==

    CASE r = 0 -> [x |-> s.x , \* Keep the values of x
                   d |-> s.d ] \* and d unchanged.
                        
    []   r = 1 -> [x |-> {}  , \* Sets x to Null (x = {})    
                   d |-> s.d ]   
                        
    []   r = 2 -> [x |-> s.x ,    
                   d |-> s.d ]   
                        
    []   r = 3 -> [x |-> s.x ,    
                   d |-> s.d ]   

                                    
==========================================================================================