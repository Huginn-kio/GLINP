(define(problem blocksplace-pro)
(:domain blocksplace)
(:init
(empty)
(not (heldX))
(not (XOnY))
( = (nx) 4)
( = (ny) 2)
)
(:goal(and(XOnY)))
)