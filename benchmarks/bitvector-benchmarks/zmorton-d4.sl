; Partially synthesize the matrix indexing function for the ZMORTON layout.
; Problem by Michael Driscoll for the CS294 Course on Program Synthesis, Fall 2012.

(set-logic BV)

(define-fun zmorton_spec ((i (BitVec 32)) (j (BitVec 32))) (BitVec 32)
 (bvor
  (bvand
   #x55555555
   (bvor
    (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF j) #x00000002) (bvand #x0000FFFF j)))
    (bvshl
     (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF j) #x00000002) (bvand #x0000FFFF j)))
     #x00000001)))
  (bvshl
   (bvand
    #x55555555
    (bvor
     (bvshl
      (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF i) #x00000002) (bvand #x0000FFFF i)))
      #x00000001)
     (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF i) #x00000002) (bvand #x0000FFFF i)))))
   #x00000001)))

(synth-fun zmorton_impl ((i (BitVec 32)) (j (BitVec 32))) (BitVec 32)
  ((Start (BitVec 32) 
   (i j #x00000001 #x00000002 #x0000FFFF #x33333333 #x55555555
    (bvand Start Start) (bvor Start Start) (bvshl Start Start)))))

(declare-var i (BitVec 32))
(declare-var j (BitVec 32))

(constraint (= (zmorton_spec i j) 
               (bvor (zmorton_impl i j)
                     (bvshl
                      (bvand
                       #x55555555
                       (bvor
                        (bvshl
                         (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF i) #x00000002) (bvand #x0000FFFF i)))
                         #x00000001)
                        (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF i) #x00000002) (bvand #x0000FFFF i)))))
                      #x00000001))))

(check-synth)    
        
; Solution:
;(define-fun zmorton_impl ((i (BitVec 32)) (j (BitVec 32))) (BitVec 32)
;  (bvand
;   #x55555555
;   (bvor
;    (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF j) #x00000002) (bvand #x0000FFFF j)))
;    (bvshl
;     (bvand #x33333333 (bvor (bvshl (bvand #x0000FFFF j) #x00000002) (bvand #x0000FFFF j)))
;     #x00000001))))