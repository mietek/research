{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("e" "⊢") ("t" "⊩")
     ("f" "𝑓") ("f2" "𝑓²") ("f3" "𝑓³") ("fn" "𝑓ⁿ")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ"))))

-}

module Try5 where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_)


data Vec (X : Set) : ℕ → Set where
  ∅   : Vec X zero
  _,_ : ∀{n} → Vec X n → X → Vec X (suc n)

data _∈_ {X : Set} : ∀{n} → X → Vec X n → Set where
  Z  : ∀{n x} {xs : Vec X n}
     → x ∈ (xs , x)
  S_ : ∀{n x y} {xs : Vec X n}
     → x ∈ xs
     → x ∈ (xs , y)


data Pr : Set where
  ⊥ : Pr

PCx : ℕ → Set
PCx = Vec Pr

infixr 1 _⊃_
data Ty {m : ℕ} (Δ : PCx m) : Set where
  𝑓_ : ∀{P} → P ∈ Δ → Ty Δ
  _⊃_ : Ty Δ → Ty Δ → Ty Δ
  ■_ : Ty Δ → Ty Δ

TCx : ∀{m} → PCx m → ℕ → Set
TCx Δ = Vec (Ty Δ)

infixl 4 _∘_
infixr 3 𝜆_
infixr 0 _⊢_
data _⊢_ {m n : ℕ} {Δ : PCx m} (Γ : TCx Δ n) : Ty Δ → Set where
  𝑣_ : ∀{A} → A ∈ Γ → Γ ⊢ A
  𝜆_ : ∀{A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⊃ B)
  _∘_ : ∀{A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B

infixr 0 ⊩_
⊩_ : Ty ∅ → Set
⊩_ A = ∀{n} {Γ : TCx ∅ n} → Γ ⊢ A

F : ∀{m} (Δ : PCx m) → Ty Δ → Set
F Δ A = ∀{n} {Γ : TCx Δ n} → Γ ⊢ A

tI : ∀{A} → ⊩ A ⊃ A
tI = 𝜆 𝑣 Z

tK : ∀{A B} → ⊩ A ⊃ B ⊃ A
tK = 𝜆 𝜆 𝑣 S Z

tS : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
tS = 𝜆 𝜆 𝜆 (𝑣 S S Z ∘ 𝑣 Z) ∘ (𝑣 S Z ∘ 𝑣 Z)

tJ : ∀{x} → F (∅ , x) (■ 𝑓 Z)
tJ = {!!}
