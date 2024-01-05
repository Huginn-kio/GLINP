(define (domain hiking2)
  (:requirements :typing :fluents)
    (:predicates
    (athn)
    (atwn)
    (attn)
    (tentup)
    (traveled)
    (energetic)
    )
   (:functions
    (numsight)
   )

    (:action drive
    :parameters  ()
    :precondition (and   (not (athn))  (not (atwn)) (not (attn))  (> (numsight) 0))
    :effect (and (athn) (attn)))

    (:action walk-back
    :parameters  ()
    :precondition (and  (athn) (not (atwn)) (attn) )
    :effect (and  (not (athn))))

    (:action walk-next
    :parameters  ()
    :precondition (and  (not (athn))  (not (atwn)) (attn))
    :effect (and (athn) (atwn)))

    (:action put-up
    :parameters  ()
    :precondition (and  (athn) (atwn) (attn) (not (tentup)))
    :effect (and (tentup)))

    (:action travel
    :parameters  ()
    :precondition (and  (not (traveled)) (tentup) (energetic))
    :effect (and (traveled) (not (energetic))))

    (:action rest
    :parameters  ()
    :precondition (and  (not (energetic)) (traveled))
    :effect (and (energetic)))

    (:action put-down
    :parameters  ()
    :precondition (and  (tentup)  (traveled) (energetic))
    :effect (and (not (tentup)) (not (athn)) (not (atwn)) (not (attn)) (not (traveled)) (decrease (numsight) 1)))
)
