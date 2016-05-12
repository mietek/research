module PHOASSTLC where


data Ty : Set where
  ⊥   : Ty
  _⊃_ : Ty → Ty → Ty

data Tm (t : Set) : Set where
  𝑣_  : t → Tm t
  𝜆_  : (t → Tm t) → Tm t
  _∘_ : Tm t → Tm t → Tm t

data ⊢_∷_ {t : Set} : Tm t → Ty → Set where
  M𝑣_  : ∀{A}  → t A  → Tm t A
  M𝜆_  : ∀{A B}  → (t A → Tm t B)  → Tm t (A ⊃ B)
  _M∘_ : ∀{A B}  → Tm t (A ⊃ B)  → Tm t A  → Tm t B
