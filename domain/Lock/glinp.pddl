(define (problem pro-lock1)
        (:domain lock1)
        (:init
            (and
              (not (gotk))
              (not (opened))
              (= (loc) (mid))
              (> (mid) 0)
              (= (xkey) (+ (mid) (mid)))
            )
        )
        (:goal (and
                    (opened)
                )
        )
)



