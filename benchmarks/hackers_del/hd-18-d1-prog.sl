; Hacker's delight 18, difficulty 1
; determine if power of two

(set-logic BV)

(define-fun hd18 ((x (BitVec 32))) Bool (and (not (bvredor (bvand (bvsub x #x00000001) x))) (bvredor x)))

(synth-fun f ((x (BitVec 32))) Bool
		   ((Start Bool ((and Start Start)
						 (not Start)
						 (or Start Start)
						 (bvredor StartBV)))
			(StartBV (BitVec 32) ((bvand StartBV StartBV)
								  (bvsub StartBV StartBV)
								  (bvadd StartBV StartBV)
								  (bvor StartBV StartBV)
								  (bvneg StartBV)
								  (bvnot StartBV)
								  (bvxor StartBV StartBV)
								  x
								  #x00000001
								  #x00000000
								  #xFFFFFFFF))))

(declare-var x (BitVec 32))
(constraint (= (hd18 x) (f x)))
(check-synth)

