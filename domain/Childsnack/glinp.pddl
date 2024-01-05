(define (problem childsnack)
        (:domain childsnack)
        (:init
            (and
              (atk)
              (= (numnsk) 0)
              (= (numgsk) 0)
              (= (numnst) 0)
              (= (numgst) 0)
              (>= (numnc) 0)
              (>= (numgc) 0)
              (> (+ (numnc) (numgc)) 0)
              (>= (numnb) (numnc))
              (>= (numni) (numnc))
              (>= (numgb) (numgc))
              (>= (numgi) (numgc))
            )
        )
        (:goal
              (and
                  (atk)
                  (= (numnc) 0)
                  (= (numgc) 0)
              )
        )
)


