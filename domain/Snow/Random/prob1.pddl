(define(problem snow_problem)
(:domain snow_domain)
(:init
(ond)
( = (lend) 1)
( = (lenw) 1)
)
(:goal(and(ond)(=(lenw)0)(=(lend)0)))
)