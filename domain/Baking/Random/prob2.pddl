(define(problem pro-baking)
(:domain baking)
(:init
(not (inep))
(not (infp))
(not (mixed))
(not (inpo))
(not (baked))
(clean)
( = (numcake) 2)
)
(:goal(and(=(numcake)0)(clean)))
)