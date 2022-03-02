(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype T ((A) (B) (C)))
(declare-datatype list ((nil2) (cons2 (head2 T) (tail2 list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom T))
   (|:+:| (|proj1-:+:| R) (|proj2-:+:| R))
   (|:>:| (|proj1-:>:| R) (|proj2-:>:| R)) (Star (proj1-Star R))))
(define-fun-rec
  splits
  ((x T) (y list2)) list2
  (match y
    ((nil nil)
     ((cons z x2)
      (match z
        (((pair2 bs cs) (cons (pair2 (cons2 x bs) cs) (splits x x2)))))))))
(define-fun-rec
  splits2
  ((x list)) list2
  (match x
    ((nil2 (cons (pair2 nil2 nil2) nil))
     ((cons2 y xs)
      (cons (pair2 nil2 (cons2 y xs)) (splits y (splits2 xs)))))))
(define-fun-rec
  or2
  ((x list3)) Bool
  (match x
    ((nil3 false)
     ((cons3 y xs) (or y (or2 xs))))))
(define-fun-rec
  eps
  ((x R)) Bool
  (match x
    ((__ false)
     (Eps true)
     ((|:+:| p q) (or (eps p) (eps q)))
     ((|:>:| r q2) (and (eps r) (eps q2)))
     ((Star y) true))))
(define-fun-rec
  okay
  ((x R)) Bool
  (match x
    ((__ true)
     ((|:+:| p q) (and (okay p) (okay q)))
     ((|:>:| r q2) (and (okay r) (okay q2)))
     ((Star p2) (and (okay p2) (not (eps p2)))))))
(define-fun-rec
  step
  ((x R) (y T)) R
  (match x
    ((__ Nil)
     ((Atom b) (ite (= b y) Eps Nil))
     ((|:+:| p q) (|:+:| (step p y) (step q y)))
     ((|:>:| r q2)
      (ite
        (eps r) (|:+:| (|:>:| (step r y) q2) (step q2 y))
        (|:+:| (|:>:| (step r y) q2) Nil)))
     ((Star p2) (|:>:| (step p2 y) (Star p2))))))
(define-fun-rec
  rec
  ((x R) (y list)) Bool
  (match y
    ((nil2 (eps x))
     ((cons2 z xs) (rec (step x z) xs)))))
(define-funs-rec
  ((reck2
    ((x R) (y list)) Bool)
   (reck
    ((p R) (q R) (x list2)) list3))
  ((match x
     ((Nil false)
      (Eps
       (match y
         ((nil2 true)
          ((cons2 z x2) false))))
      ((Atom c)
       (match y
         ((nil2 false)
          ((cons2 b2 x3)
           (match x3
             ((nil2 (= c b2))
              ((cons2 x4 x5) false)))))))
      ((|:+:| p q) (or (reck2 p y) (reck2 q y)))
      ((|:>:| r q2) (or2 (reck r q2 (splits2 y))))
      ((Star p2)
       (match y
         ((nil2 true)
          ((cons2 x6 x7)
           (ite
             (not (eps p2)) (rec (|:>:| p2 (Star p2)) (cons2 x6 x7))
             false)))))))
   (match x
     ((nil nil3)
      ((cons y z)
       (match y
         (((pair2 l r)
           (cons3 (and (reck2 p l) (rec q r)) (reck p q z))))))))))
(assert
  (not
    (forall ((p R) (s list)) (=> (okay p) (= (rec p s) (reck2 p s))))))
(check-sat)
