(declare-sort sk 0)
(declare-datatype
  Tree
  ((Leaf)
   (Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(define-fun-rec
  mirror
  ((x Tree)) Tree
  (match x
    ((Leaf Leaf)
     ((Node l y r) (Node (mirror r) y (mirror l))))))
(define-fun-rec
  max
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z)
      (match y
        ((Z (S z))
         ((S x2) (S (max z x2)))))))))
(define-fun-rec
  height
  ((x Tree)) Nat
  (match x
    ((Leaf Z)
     ((Node l y r) (S (max (height l) (height r)))))))
(assert
  (not (forall ((a1 Tree)) (= (height (mirror a1)) (height a1)))))
(check-sat)
