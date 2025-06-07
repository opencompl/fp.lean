(set-info :smt-lib-version 2.6)
(set-logic FP)

(define-sort FP () (_ FloatingPoint 3 5))

(declare-const a FP)
(declare-const b FP)
(declare-const c FP)

(assert
 (not (or (not (and (fp.leq a b) (not (or (fp.isInfinite c) (fp.isNaN c)))) )
    (fp.leq (fp.add RNE a c) (fp.add RNE b c))
 ))
)

(set-info :status unknown)
(check-sat)
(exit)