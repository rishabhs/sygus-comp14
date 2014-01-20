(set-logic LIA)

(synth-fun f1 ((p1 Int) (P1 Int) (N1 Int)) Int
	   ((Start Int (
			p1
			P1
			N1
			(/ N1 P1)
			(% N1 P1)
			(* Start Start)
			(+ Start Start)
                     )
           )))

(synth-fun f2 ((p1 Int) (P1 Int) (N1 Int)) Int
	   ((Start Int (
			p1
			P1
			N1
			(/ N1 P1)
			(% N1 P1)
			(* Start Start)
			(+ Start Start)
                     )
           )))
(synth-fun f3 ((p1 Int) (P1 Int) (N1 Int)) Int
	   ((Start Int (
			p1
			P1
			N1
			(/ N1 P1)
			(% N1 P1)
			(* Start Start)
			(+ Start Start)
                     )
           )))
(synth-fun f4 ((p1 Int) (P1 Int) (N1 Int)) Int
	   ((Start Int (
			p1
			P1
			N1
			(/ N1 P1)
			(% N1 P1)
			(* Start Start)
			(+ Start Start)
                     )
           )))
(synth-fun f5 ((p1 Int) (P1 Int) (N1 Int)) Int
	   ((Start Int (
			p1
			P1
			N1
			(/ N1 P1)
			(% N1 P1)
			(* Start Start)
			(+ Start Start)
                     )
           )))

(declare-var p Int)
(declare-var N Int)
(declare-var P Int)

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< p P)) 
	    (< (- (ite (< p (f1 p P N)) (f2 p P N) (f4 p P N)) (ite (< p (f1 p P N)) (f3 p P N) (f5 p P N))) (+ (/ N P) 2))))

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< (+ p 1) P))
	       (= (ite (< p (f1 p P N)) (f2 p P N) (f4 p P N)) (ite (< (+ p 1) (f1 (+ p 1) P N)) (f3 (+ p 1) P N) (f5 (+ p 1) P N)))) )

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< p P)) 
	       (and (=> (= p 0) (= (ite (< p (f1 p P N)) (f3 p P N) (f5 p P N)) 0))
	       	    (=> (= p (- P 1)) (= (ite (< p (f1 p P N)) (f2 p P N) (f4 p P N)) N)))))
(check-synth)