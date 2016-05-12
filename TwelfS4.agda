module TwelfS4 where

data o : Set where
  ¬ : o → o
  ⊃ : o → o → o
  □ : o → o

data _hl⊢_ :
