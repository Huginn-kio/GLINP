(define(problem intrusion1-pro)
(:domain intrusion1)
(:init
( = (numhost) 2)
( = (numcon) 0)
( = (numbrk) 0)
( = (numcln) 0)
( = (numgained) 0)
( = (numdown) 0)
( = (numstl) 0)
)
(:goal(and(=(numstl)(numhost))))
)