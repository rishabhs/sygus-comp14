(set-logic LIA)

(synth-fun axpb ((x Int)) Int
	   (
	   (Start Int (
	   	      (let ((y Int CInt) (z Int CInt)) (+ (* y x) z))
	   	      )
 	   )
	   (CInt Int (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))

	   )
)

(declare-var x1 Int)
(declare-var x2 Int)

(constraint (= (* (axpb x1) (axpb x2)) (* (+ x1 x1) (+ x2 5))))