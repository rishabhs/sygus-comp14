; Hacker's delight 18, minimal grammar
; determine if power of two

(set-logic BV)

(define-fun hd18 ((x (BitVec 32))) Bool (and (not (bvredor (bvand (bvsub x #x00000001) x))) (bvredor x)))

(synth-fun f ((x (BitVec 32))) Bool
		   ((Start Bool ((and Start Start)
						 (not Start)
						 (bvredor StartBV)))
			(StartBV (BitVec 32) ((bvand StartBV StartBV)
								  (bvsub StartBV StartBV)
								  x
								  #x00000001))))

(declare-var x (BitVec 32))
(constraint (= (hd18 x) (f x)))
(check-synth)

