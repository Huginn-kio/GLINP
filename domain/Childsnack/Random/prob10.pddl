(define(problem childsnack)
(:domain childsnack)
(:init
(atk)
( = (numnb) 1)
( = (numni) 4)
( = (numgb) 2)
( = (numgi) 2)
( = (numnc) 1)
( = (numgc) 2)
( = (numnsk) 0)
( = (numgsk) 0)
( = (numnst) 0)
( = (numgst) 0)
)
(:goal(and(atk)(=(numnc)0)(=(numgc)0)))
)