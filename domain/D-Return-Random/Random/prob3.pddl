(define(problem pro-Diagonal-Return-Random)
(:domain Diagonal-Return-Random)
(:init
(not (dectr))
(not (dectl))
(dectt)
(not (dectb))
(not (visitlt))
(not (visitrt))
(not (visitrb))
( = (disr) 1)
( = (disl) 3)
( = (dist) 1)
( = (disb) 1)
( = (startt) 1)
( = (startl) 3)
)
(:goal(and(visitlt)(visitrt)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)