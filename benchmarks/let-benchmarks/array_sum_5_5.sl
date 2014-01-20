;; expected program:: (let ((z Int (+ x1 x2))) (ite (> z 5) z (
;;   	    	      let ((z Int (+ x2 x3))) (ite (> z 5) z (
;;   	    	      let ((z Int (+ x3 x4))) (ite (> z 5) z (
;;   	    	      let ((z Int (+ x4 x5))) (ite (> z 5) z 0))))))))



(set-logic LIA)
(synth-fun findSum ((y1 Int) (y2 Int) (y3 Int) (y4 Int) (y5 Int)) Int 
           ((Start Int (0 
                        1
                        2
                        3
                        4
                        5 
                        y1 
                        y2 
                        y3 
                        y4 
			y5
                        z 
			(+ Start Start)
                        (let ((z Int Start)) Start) 
                        (ite BoolExpr Start Start))) 
            (BoolExpr Bool 
                      ((< Start Start) 
                       (<= Start Start) 
                       (> Start Start) 
                       (>= Start Start)))))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)

(constraint (=> (> (+ x1 x2) 5) (= (findSum x1 x2 x3 x4 x5) (+ x1 x2))))
(constraint (=> (and (<= (+ x1 x2) 5) (> (+ x2 x3) 5)) (= (findSum x1 x2 x3 x4 x5) (+ x2 x3))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (<= (+ x2 x3) 5)) (> (+ x3 x4) 5)) (= (findSum x1 x2 x3 x4 x5) (+ x3 x4))))
(constraint (=> (and (and (and (<= (+ x1 x2) 5) (<= (+ x2 x3) 5)) (<= (+ x3 x4) 5)) (> (+x4 x5) 5)) (= (findSum x1 x2 x3 x4 x5) (+ x4 x5))))
(constraint (=> (and (and (and (<= (+ x1 x2) 5) (<= (+ x2 x3) 5)) (<= (+ x3 x4) 5)) (<= (+x4 x5) 5)) (= (findSum x1 x2 x3 x4 x5) 0)))

(check-synth)
