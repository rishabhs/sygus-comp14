(set-logic BV)

(synth-fun countSketch ((x (BitVec 8))) (BitVec 8)
	   (
	     (Start (BitVec 8) ( x
	     	     	       	 (let ((tmp (BitVec 8) Start) (m (BitVec 8) ConstBV) (n (BitVec 8) ConstBV)) (bvadd (bvand tmp m) (bvand (bvshr tmp n) m)) )
                
		)
	     )
	     (ConstBV (BitVec 8) (
	        #x00 #xAA #xCC #xE0
    		 )
	     
	     )
	   )
)


(declare-var x1 (BitVec 8))

(declare-fun res0 () (BitVec 8))
(declare-fun res1 () (BitVec 8))
(declare-fun res2 () (BitVec 8))
(declare-fun res3 () (BitVec 8))
(declare-fun res4 () (BitVec 8))
(declare-fun res5 () (BitVec 8))
(declare-fun res6 () (BitVec 8))
(declare-fun res7 () (BitVec 8))
(declare-fun res8 () (BitVec 8))

(constraint (= res0 #x00))
(constraint (=> (= (bvand x1 #x01) #x01) (= res1 (bvadd res0 #x01))))
(constraint (=> (= (bvand x1 #x01) #x00) (= res1 res0)))

(constraint (=> (= (bvand x1 #x02) #x01) (= res2 (bvadd res1 #x01))))
(constraint (=> (= (bvand x1 #x02) #x00) (= res2 res1)))

(constraint (=> (= (bvand x1 #x04) #x01) (= res3 (bvadd res2 #x01))))
(constraint (=> (= (bvand x1 #x04) #x00) (= res3 res2)))

(constraint (=> (= (bvand x1 #x08) #x01) (= res4 (bvadd res3 #x01))))
(constraint (=> (= (bvand x1 #x08) #x00) (= res4 res3)))

(constraint (=> (= (bvand x1 #x10) #x01) (= res5 (bvadd res4 #x01))))
(constraint (=> (= (bvand x1 #x10) #x00) (= res5 res4)))

(constraint (=> (= (bvand x1 #x20) #x01) (= res6 (bvadd res5 #x01))))
(constraint (=> (= (bvand x1 #x20) #x00) (= res6 res5)))

(constraint (=> (= (bvand x1 #x40) #x01) (= res7 (bvadd res6 #x01))))
(constraint (=> (= (bvand x1 #x40) #x00) (= res7 res6)))

(constraint (=> (= (bvand x1 #x80) #x01) (= res8 (bvadd res7 #x01))))
(constraint (=> (= (bvand x1 #x80) #x00) (= res8 res7)))

(constraint (= res8 (countSketch x1)))

(check-synth)
