module IAmNotANumber where

infixl 9 _$_
infixr 6 _⊃_

data Expr : Set where
  F : Name → Expr
  B : Int → Expr
  _$_ : Expr → Expr → Expr
  _⊃_ : Expr → Scope → Expr
