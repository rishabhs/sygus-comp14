(set-logic LIA)

;; rec(x,y,z) \equiv (* (+ x x) (- y z))

(synth-fun rec ((x Int) (y Int) (z Int)) Int
	   (
	   (Start Int (x
	               y
   		       z
		       (* Start Start)
		       (+ Start Start)
		       (- Start Start)
	   ))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (rec x1 x2 x3) (* (+ x1 x1) (- x2 x3))))

(check-synth)