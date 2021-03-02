(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list)
(define-fun
  return
  ((x sk)) list (cons x nil))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-fun-rec
  >>=
  ((x list) (y fun12)) list
  (match x
    ((nil nil)
     ((cons z xs) (++ (apply12 y z) (>>= xs y))))))
(assert (forall ((x sk)) (= (apply12 lam x) (return x))))
(assert (not (forall ((xs list)) (= (>>= xs lam) xs))))
(check-sat)
