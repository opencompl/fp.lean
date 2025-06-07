(set-info :smt-lib-version 2.6)
(set-logic FP)

(define-sort FP () (_ FloatingPoint 3 5))

(declare-const x FP)
(declare-const y FP)

(assert
 (not (= (fp.mul RNE x y) (fp.mul RNE y x)))
)

(set-info :status unknown)
(check-sat)
(exit)