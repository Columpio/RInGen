(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(declare-datatype list ((nil) (cons (head Tree) (tail list))))
(declare-const lam fun13)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list2)
(declare-fun apply13 (fun13 Tree) list2)
(define-fun-rec
  flatten1
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y ps)
      (match y
        (((Node z x2 q)
          (match z
            (((Node x3 x4 x5)
              (flatten1 (cons (Node x3 x4 x5) (cons (Node Nil x2 q) ps))))
             (Nil (cons2 x2 (flatten1 (cons q ps)))))))
         (Nil (flatten1 ps))))))))
(define-fun-rec
  ++
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun-rec
  concatMap
  ((f fun13) (x list)) list2
  (match x
    ((nil nil2)
     ((cons y xs) (++ (apply13 f y) (concatMap f xs))))))
(define-fun-rec
  concatMap2
  ((f fun12) (x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (++ (apply12 f y) (concatMap2 f xs))))))
(define-fun-rec
  flatten0
  ((x Tree)) list2
  (match x
    (((Node p y q) (++ (flatten0 p) (++ (cons2 y nil2) (flatten0 q))))
     (Nil nil2))))
(assert (forall ((x Tree)) (= (apply13 lam x) (flatten0 x))))
(assert
  (not (forall ((ps list)) (= (flatten1 ps) (concatMap lam ps)))))
(check-sat)
