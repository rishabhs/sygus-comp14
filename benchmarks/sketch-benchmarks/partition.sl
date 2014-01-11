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

(declare-fun ibeg () Int)
(declare-fun iend () Int)
(declare-fun ibeg2 () Int)
(declare-fun iend2 () Int)

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< p P)) 
	    (and (= ibeg (ite (< p (f1 p P N)) (f3 p P N) (f5 p P N)))
	    	 (= iend (ite (< p (f1 p P N)) (f2 p P N) (f4 p P N))))))
(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< p P)) 
	    (< (- iend ibeg) (+ (/ N P) 2))))

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< (+ p 1) P)) 
	    (and (= ibeg2 (ite (< (+ p 1) (f1 (+ p 1) P N)) (f3 (+ p 1) P N) (f5 (+ p 1) P N)))
	    	 (= iend2 (ite (< (+ p 1) (f1 (+ p 1) P N)) (f2 (+ p 1) P N) (f4 (+ p 1) P N))))))

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< (+ p 1) P))
	       (= iend ibeg2)) )

(constraint( => (and (and (and (>= p 0) (> N 0)) (> P 0)) (< p P)) 
	       (and (=> (= p 0) (= ibeg 0))
	       	    (=> (= p (- P 1)) (= iend N)))))
(check-synth)