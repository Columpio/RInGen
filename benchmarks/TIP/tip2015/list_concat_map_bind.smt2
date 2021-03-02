(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list2)
(define-fun-rec
  map3
  ((f fun1) (x list2)) list2
  (match x
    ((nil2 nil2)
     ((cons2 y xs) (cons2 (apply1 f y) (map3 f xs))))))
(define-fun-rec
  map2
  ((f fun12) (x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y xs) (cons (apply12 f y) (map2 f xs))))))
(define-fun-rec
  ++
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z xs) (cons2 z (++ xs y))))))
(define-fun-rec
  >>=
  ((x list2) (y fun12)) list2
  (match x
    ((nil2 nil2)
     ((cons2 z xs) (++ (apply12 y z) (>>= xs y))))))
(define-fun-rec
  concat2
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons y xs) (++ y (concat2 xs))))))
(assert
  (not
    (forall ((f fun12) (xs list2))
      (= (concat2 (map2 f xs)) (>>= xs f)))))
(check-sat)
