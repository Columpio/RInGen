(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype
  E
  ((N (proj1-N Int)) (Add (proj1-Add E) (proj2-Add E))
   (Mul (proj1-Mul E) (proj2-Mul E)) (Eq (proj1-Eq E) (proj2-Eq E))
   (V (proj1-V Int))))
(declare-datatypes ((P 0) (list 0))
  (((Print (proj1-Print E)) (|:=| (|proj1-:=| Int) (|proj2-:=| E))
    (While (proj1-While E) (proj2-While list))
    (If (proj1-If E) (proj2-If list) (proj3-If list)))
   ((nil) (cons (head P) (tail list)))))
(define-fun-rec
  store2
  ((x list2) (y Int) (z Int)) list2
  (match x
    ((nil2
      (ite (= y 0) (cons2 z nil2) (cons2 0 (store2 nil2 (- y 1) z))))
     ((cons2 n st)
      (ite (= y 0) (cons2 z st) (cons2 n (store2 st (- y 1) z)))))))
(define-fun-rec
  fetch
  ((x list2) (y Int)) Int
  (match x
    ((nil2 0)
     ((cons2 n st) (ite (= y 0) n (fetch st (- y 1)))))))
(define-fun-rec
  eval
  ((x list2) (y E)) Int
  (match y
    (((N n) n)
     ((Add a b) (+ (eval x a) (eval x b)))
     ((Mul c b2) (* (eval x c) (eval x b2)))
     ((Eq a2 b3) (ite (= (eval x a2) (eval x b3)) 1 0))
     ((V z) (fetch x z)))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun
  opti
  ((x P)) P
  (match x
    ((_ x)
     ((While e p) (While e (++ p p)))
     ((If c q r) (If c r q)))))
(define-fun-rec
  run
  ((x list2) (y list)) list2
  (match y
    ((nil nil2)
     ((cons z r)
      (match z
        (((Print e) (cons2 (eval x e) (run x r)))
         ((|:=| x2 e2) (run (store2 x x2 (eval x e2)) r))
         ((While e3 p)
          (run x (cons (If e3 (++ p (cons (While e3 p) nil)) nil) r)))
         ((If e4 q q2)
          (ite (= (eval x e4) 0) (run x (++ q2 r)) (run x (++ q r))))))))))
(assert
  (not
    (forall ((p P))
      (= (run nil2 (cons p nil)) (run nil2 (cons (opti p) nil))))))
(check-sat)
