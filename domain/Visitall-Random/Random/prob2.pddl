(define(problem pro-visitall-Random)
(:domain visitall-Random)
(:init
(not (visitr))
(not (visitl))
(not (dectr))
(not (dectl))
(not (dectt))
(dectb)
( = (disr) 2)
( = (disb) 2)
( = (disl) 0)
( = (dist) 0)
( = (numr) 0)
)
(:goal(and(=(numr)(+(disb)(dist)))))
)