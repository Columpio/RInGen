(declare-datatype Tok ((X) (Y) (Z)))
(declare-datatype list ((nil) (cons (head Tok) (tail list))))
(declare-datatype B2 ((SB (proj1-SB B2)) (ZB)))
(declare-datatype A2 ((SA (proj1-SA A2)) (ZA)))
(declare-datatype S ((A (proj1-A A2)) (B (proj1-B B2))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  linA
  ((x A2)) list
  (match x
    (((SA a) (++ (cons X nil) (++ (linA a) (cons Y nil))))
     (ZA (cons X (cons Z (cons Y nil)))))))
(define-fun-rec
  linB
  ((x B2)) list
  (match x
    (((SB b) (++ (cons X nil) (++ (linB b) (cons Y (cons Y nil)))))
     (ZB (cons X (cons Z (cons Y (cons Y nil))))))))
(define-fun
  linS
  ((x S)) list
  (match x
    (((A a) (linA a))
     ((B b) (linB b)))))
(assert
  (not (forall ((u S) (v S)) (=> (= (linS u) (linS v)) (= u v)))))
(check-sat)
