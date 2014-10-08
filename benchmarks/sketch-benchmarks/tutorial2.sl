(set-logic LIA)

;; axpb1  \equiv (let ((y Int 1) (z Int 0) (+ (* y x) z)))
;; axpb2  \equiv (let ((y Int 2) (z Int 10) (+ (* y x) z)))


(synth-fun axpb1 ((x Int)) Int
	   (
	   (Start Int (
	   	      (let ((y Int CInt) (z Int CInt)) (+ (* y x) z))
	   	      )
 	   )
	   (CInt Int (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))

	   )
)

(synth-fun axpb2 ((x Int)) Int
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

(constraint (= (* (axpb1 x1) (axpb2 x2)) (* (+ x1 x1) (+ x2 5))))

(check-synth)