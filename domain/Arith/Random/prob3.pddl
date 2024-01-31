(define(problem arith-pro)
(:domain arith)
(:init
( = (n) 3)
( = (v1) 0)
( = (v2) 0)
)
(:goal(and(=(v1)(n))(=(v2)(+(n)(+(n)1)))))
)