; Hacker's delight 10, minimal grammar
; Test if (nlz x) == (nlz y) where nlz is the number of leading zeros

(set-logic BV)

(define-fun hd10 ((x (BitVec 32)) (y (BitVec 32))) Bool (bvule (bvand x y) (bvxor x y)))

(synth-fun f ((x (BitVec 32)) (y (BitVec 32))) Bool
    ((Start Bool ((bvule StartBV StartBV)
				  (bvsle StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvand StartBV StartBV)
						   (bvxor StartBV StartBV)
						   (bvor StartBV StartBV)
						   (bvadd StartBV StartBV)
						   (bvsub StartBV StartBV)
						   (bvnot StartBV)
						   (bvneg StartBV)
						   x
						   y))))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(constraint (= (hd10 x y) (f x y)))
(check-synth)

