; Hacker's delight 11, difficulty 1
; Test if (nlz x) < (nlz y) where nlz is the number of leading zeros

(set-logic BV)

(define-fun hd11 ((x (BitVec 32)) (y (BitVec 32))) Bool (bvugt (bvand x (bvnot y)) y))

(synth-fun f ((x (BitVec 32)) (y (BitVec 32))) Bool
    ((Start Bool ((bvugt StartBV StartBV)
				  (bvuge StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvand StartBV StartBV)
						   (bvor StartBV StartBV)
						   (bvxor StartBV StartBV)
						   (bvadd StartBV StartBV)
						   (bvsub StartBV StartBV)
						   (bvnot StartBV)
						   (bvneg StartBV)
						   #x00000000
						   #x00000001
						   #xFFFFFFFF
						   x
						   y))))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(constraint (= (hd11 x y) (f x y)))
(check-synth)

