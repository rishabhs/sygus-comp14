; Hacker's delight 12, minimal grammar
; Test if (nlz x) <= (nlz y) where nlz is the number of leading zeros

(set-logic BV)

(define-fun hd12 ((x (BitVec 32)) (y (BitVec 32))) Bool (bvule (bvand x (bvnot y)) y))

(synth-fun f ((x (BitVec 32)) (y (BitVec 32))) Bool
    ((Start Bool ((bvule StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvand StartBV StartBV)
						   (bvnot StartBV)
						   x
						   y))))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(constraint (= (hd12 x y) (f x y)))
(check-synth)

