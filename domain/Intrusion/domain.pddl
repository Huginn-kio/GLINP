(define (domain intrusion1)
(:requirements :typing :fluents)

(:functions
    (numhost)
    (numcon)
    (numbrk)
    (numcln)
    (numgained)
    (numdown)
    (numstl)
)

(:action recon
       :parameters  ()
       :precondition (and (< (numcon) (numhost)))
       :effect (and  (increase (numcon) 1) )
)

(:action break
       :parameters  ()
       :precondition (and  (< (numbrk) (numcon)))
       :effect (and  (increase (numbrk) 1) )
)

(:action clean
       :parameters  ()
       :precondition (and  (< (numcln) (numbrk)))
       :effect (and  (increase (numcln) 1) )
)

(:action gain
       :parameters  ()
       :precondition (and  (< (numgained) (numcln)))
       :effect (and   (increase (numgained) 1) )
)

(:action download
       :parameters  ()
       :precondition (and  (< (numdown) (numgained)))
       :effect (and (increase (numdown) 1))
)

(:action steal
       :parameters  ()
       :precondition (and  (< (numstl) (numdown)))
       :effect (and (increase (numstl) 1))
)
)


