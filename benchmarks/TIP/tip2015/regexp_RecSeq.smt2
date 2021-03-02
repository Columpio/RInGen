(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype A ((X) (Y)))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom A))
   (Plus (proj1-Plus R) (proj2-Plus R))
   (Seq (proj1-Seq R) (proj2-Seq R)) (Star (proj1-Star R))))
(declare-datatype list ((nil2) (cons2 (head2 A) (tail2 list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(define-fun-rec
  split
  ((x A) (y list2)) list2
  (match y
    ((nil nil)
     ((cons z x2)
      (match z
        (((pair2 xs ys) (cons (pair2 (cons2 x xs) ys) (split x x2)))))))))
(define-fun-rec
  split2
  ((x list)) list2
  (match x
    ((nil2 (cons (pair2 nil2 nil2) nil))
     ((cons2 y s)
      (cons (pair2 nil2 (cons2 y s)) (split y (split2 s)))))))
(define-fun
  seq
  ((x R) (y R)) R
  (match x
    ((_
      (match y
        ((_
          (match x
            ((_
              (match y
                ((_ (Seq x y))
                 (Eps x))))
             (Eps y))))
         (Nil Nil))))
     (Nil Nil))))
(define-fun
  plus
  ((x R) (y R)) R
  (match x
    ((_
      (match y
        ((_ (Plus x y))
         (Nil x))))
     (Nil y))))
(define-fun-rec
  or2
  ((x list3)) Bool
  (match x
    ((nil3 false)
     ((cons3 y xs) (or y (or2 xs))))))
(define-fun
  eqA
  ((x A) (y A)) Bool
  (match x
    ((X
      (match y
        ((X true)
         (Y false))))
     (Y
      (match y
        ((X false)
         (Y true)))))))
(define-fun-rec
  eps
  ((x R)) Bool
  (match x
    ((_ false)
     (Eps true)
     ((Plus p q) (or (eps p) (eps q)))
     ((Seq r q2) (and (eps r) (eps q2)))
     ((Star y) true))))
(define-fun
  epsR
  ((x R)) R (ite (eps x) Eps Nil))
(define-fun-rec
  step
  ((x R) (y A)) R
  (match x
    ((_ Nil)
     ((Atom a) (ite (eqA a y) Eps Nil))
     ((Plus p q) (plus (step p y) (step q y)))
     ((Seq r q2) (plus (seq (step r y) q2) (seq (epsR r) (step q2 y))))
     ((Star p2) (seq (step p2 y) (Star p2))))))
(define-fun-rec
  recognise
  ((x R) (y list)) Bool
  (match y
    ((nil2 (eps x))
     ((cons2 z xs) (recognise (step x z) xs)))))
(define-fun-rec
  formula
  ((p R) (q R) (x list2)) list3
  (match x
    ((nil nil3)
     ((cons y z)
      (match y
        (((pair2 s1 s2)
          (cons3 (and (recognise p s1) (recognise q s2))
            (formula p q z)))))))))
(assert
  (not
    (forall ((p R) (q R) (s list))
      (= (recognise (Seq p q) s) (or2 (formula p q (split2 s)))))))
(check-sat)
