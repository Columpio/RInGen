(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun lam (fun12 fun12) fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list)
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
(assert
  (forall ((f fun12) (g fun12) (x sk))
    (= (apply12 (lam f g) x) (>>= (apply12 f x) g))))
(assert
  (not
    (forall ((m list) (f fun12) (g fun12))
      (= (>>= (>>= m f) g) (>>= m (lam f g))))))
(check-sat)
