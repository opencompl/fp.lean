(set-info :smt-lib-version 2.6)
(set-logic FP)

(define-sort FP () (_ FloatingPoint 3 5))
(define-fun twoE3M4 () FP (fp #b0 #b100 #b0000))

(declare-const a FP)

(assert
    (not (= (fp.add RNE a a) (fp.mul RNE a twoE3M4)))
)

(set-info :status unknown)
(check-sat)
(exit)