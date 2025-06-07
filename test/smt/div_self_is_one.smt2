(set-info :smt-lib-version 2.6)
(set-logic FP)

(define-sort FP () (_ FloatingPoint 3 5))
(define-fun oneE3M4 () FP (fp #b0 #b011 #b0000))

(declare-const a FP)

(assert
 (not (or (fp.isNaN a) (fp.isInfinite a) (fp.isZero a)
    (= (fp.div RNE a a) oneE3M4)
 ))
)

(set-info :status unknown)
(check-sat)
(exit)