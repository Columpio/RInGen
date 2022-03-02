(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list ((nil2) (cons2 (head2 sk) (tail2 list))))
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 pair) sk)
(define-fun-rec
  select2
  ((x sk) (y list2)) list2
  (match y
    ((nil nil)
     ((cons z x2)
      (match z
        (((pair2 y2 ys)
          (cons (pair2 y2 (cons2 x ys)) (select2 x x2)))))))))
(define-fun-rec
  select22
  ((x list)) list2
  (match x
    ((nil2 nil)
     ((cons2 y xs) (cons (pair2 y xs) (select2 y (select22 xs)))))))
(define-fun-rec
  map3
  ((f fun1) (x list)) list
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (cons2 (apply1 f y) (map3 f xs))))))
(define-fun-rec
  map2
  ((f fun12) (x list2)) list
  (match x
    ((nil nil2)
     ((cons y xs) (cons2 (apply12 f y) (map2 f xs))))))
(assert
  (forall ((x pair))
    (= (apply12 lam x) (match x (((pair2 y z) y))))))
(assert (not (forall ((xs list)) (= (map2 lam (select22 xs)) xs))))
(check-sat)
