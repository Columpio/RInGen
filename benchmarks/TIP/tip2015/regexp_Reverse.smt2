(declare-datatype A ((X) (Y)))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom A))
   (Plus (proj1-Plus R) (proj2-Plus R))
   (Seq (proj1-Seq R) (proj2-Seq R)) (Star (proj1-Star R))))
(declare-datatype list ((nil) (cons (head A) (tail list))))
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
(define-fun-rec
  rev
  ((x R)) R
  (match x
    ((_ x)
     ((Plus a b) (Plus (rev a) (rev b)))
     ((Seq c b2) (Seq (rev b2) (rev c)))
     ((Star a2) (Star (rev a2))))))
(define-fun
  plus
  ((x R) (y R)) R
  (match x
    ((_
      (match y
        ((_ (Plus x y))
         (Nil x))))
     (Nil y))))
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
    ((nil (eps x))
     ((cons z xs) (recognise (step x z) xs)))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  reverse
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs) (++ (reverse xs) (cons y nil))))))
(assert
  (not
    (forall ((r R) (s list))
      (= (recognise (rev r) s) (recognise r (reverse s))))))
(check-sat)
