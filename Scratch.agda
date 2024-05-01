module Scratch where


{-

How can we implement quasiquotation?

When we evaluate
  (letbox (box (app (lam vz) M)) (box (pair mvz (app (lam vz) N))))
normally, we get
  (box (pair (app (lam vz) M) (app (lam vz) N)))
.

We would like to somehow insert the result of evaluating
  (app (lam vz) M)
into the final result, getting
  (box (pair M (app (lam vz) N)))
.

We don't want to collapse the entire final result and get
  (pair M N)
.

-}
