(declare-datatype T ((A) (B) (C)))
(declare-datatype list ((nil) (cons (head T) (tail list))))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom T))
   (|:+:| (|proj1-:+:| R) (|proj2-:+:| R))
   (|:&:| (|proj1-:&:| R) (|proj2-:&:| R))
   (|:>:| (|proj1-:>:| R) (|proj2-:>:| R)) (Star (proj1-Star R))))
(define-fun
  x.>.
  ((x R) (y R)) R
  (match x
    ((_
      (match y
        ((_
          (match x
            ((_
              (match y
                ((_ (|:>:| x y))
                 (Eps x))))
             (Eps y))))
         (Nil Nil))))
     (Nil Nil))))
(define-fun
  x.+.
  ((x R) (y R)) R
  (match x
    ((_
      (match y
        ((_ (|:+:| x y))
         (Nil x))))
     (Nil y))))
(define-fun-rec
  eps
  ((x R)) Bool
  (match x
    ((_ false)
     (Eps true)
     ((|:+:| p q) (or (eps p) (eps q)))
     ((|:&:| r q2) (and (eps r) (eps q2)))
     ((|:>:| p2 q3) (and (eps p2) (eps q3)))
     ((Star y) true))))
(define-fun-rec
  step
  ((x R) (y T)) R
  (match x
    ((_ Nil)
     ((Atom b) (ite (= b y) Eps Nil))
     ((|:+:| p q) (x.+. (step p y) (step q y)))
     ((|:&:| r q2)
      (let ((wild1 (step r y)))
        (match wild1
          ((_
            (let ((wild2 (step q2 y)))
              (match wild2
                ((_ (|:&:| wild1 wild2))
                 (Nil Nil)))))
           (Nil Nil)))))
     ((|:>:| p2 q3)
      (ite
        (eps p2) (x.+. (x.>. (step p2 y) q3) (step q3 y))
        (x.+. (x.>. (step p2 y) q3) Nil)))
     ((Star p3) (x.>. (step p3 y) (Star p3))))))
(define-fun-rec
  rec
  ((x R) (y list)) Bool
  (match y
    ((nil (eps x))
     ((cons z xs) (rec (step x z) xs)))))
(assert
  (not
    (forall ((p R) (q R) (s list))
      (= (rec (|:+:| p q) s) (rec (|:>:| p q) s)))))
(check-sat)
