; Hacker's delight 18, difficulty 5
; determine if power of two

(set-logic BV)

(define-fun hd18 ((x (BitVec 32))) Bool (and (not (bvredor (bvand (bvsub x #x00000001) x))) (bvredor x)))

(synth-fun f ((x (BitVec 32))) Bool
    ((Start Bool ((bvule StartBV StartBV)
				  (bvult StartBV StartBV)
				  (bvslt StartBV StartBV)
				  (bvsle StartBV StartBV)
				  (= StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvnot StartBV)
						   (bvxor StartBV StartBV)
						   (bvand StartBV StartBV)
						   (bvor StartBV StartBV)
						   (bvneg StartBV)
						   (bvadd StartBV StartBV)
						   (bvmul StartBV StartBV)
						   (bvudiv StartBV StartBV)
						   (bvurem StartBV StartBV)
						   (bvlshr StartBV StartBV)
						   (bvashr StartBV StartBV)
						   (bvshl StartBV StartBV)
						   (bvsdiv StartBV StartBV)
						   (bvsrem StartBV StartBV)
						   (bvsub StartBV StartBV)
						   x))))

(declare-var x (BitVec 32))
(constraint (= (hd18 x) (f x)))
(check-synth)

