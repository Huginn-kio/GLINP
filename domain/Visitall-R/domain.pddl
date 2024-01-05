(define (domain visitall-R)
  (:requirements :typing :fluents)
  (:predicates 
    (visitr)
    (visitl)
    (dectr)
    (dectl)
    (dectt)
    (dectb)
  )

(:functions 
    (disr)
    (disl)
    (dist)
    (disb)
    (numr)
)
      (:action forward
       :parameters  ()
       :precondition (and   )
       :effect (and  
          (when (and (dectr)  (> (disr) 0))  (and  (decrease (disr) 1) (increase (disl) 1)))
          (when (and (dectl)  (> (disl) 0))  (and  (decrease (disl) 1) (increase (disr) 1)))
          (when (and (dectt)  (> (dist) 0))  (and  (decrease (dist) 1) (increase (disb) 1)))
         (when (and (dectb)  (> (disb) 0) (visitr) (visitl) (= (disl) 0) )  (and  (decrease (disb) 1) (increase (dist) 1)  (not (visitr)) (not (visitl) ))
          )
          )
      )
       (:action turnL
       :parameters  ()
       :precondition (and  )
       :effect (and  
          (when (and (dectr))  (and  (not (dectr)) (dectt)))
          (when (and (dectl))  (and  (not (dectl)) (dectb)))
          (when (and (dectb))  (and  (not (dectb)) (dectr)))
	  (when (and (dectt))  (and  (not (dectt)) (dectl)))
	))
       (:action turnR
       :parameters  ()
       :precondition (and   )
       :effect (and  
          (when (and (dectr))  (and  (not (dectr)) (dectb)))
          (when (and (dectl))  (and  (not (dectl)) (dectt)))
          (when (and (dectb))  (and  (not (dectb)) (dectl)))
	  (when (and (dectt))  (and  (not (dectt)) (dectr)))
       )) 

          
(:action Markl
:parameters  ()
:precondition (and  (= (disl) 0)  (not (visitl)) (visitr))
:effect (and  (visitl) (increase (numr) 1)
  ))

(:action Markr
:parameters  ()
:precondition (and  (= (disr) 0)  (not (visitr)) (not (visitl)))
:effect (and  (visitr) 
  ))

)
