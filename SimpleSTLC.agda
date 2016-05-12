module SimpleSTLC where

open import Data.Nat using (ℕ ; zero ; suc ; _⊔_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

infixl 9 𝑣_ 𝒗_
infixl 7 _∘_ _∙_
infixr 5 𝜆_ 𝝀_
infixr 4 ¬_
infixl 3 _,_ _„_
infixr 2 _⊃_
infixr 0 _⊢_∷_ ⊩_∷_


data Tm : ℕ → Set where
  𝑣_  : (x : ℕ) → Tm (suc x)
  𝜆_  : ∀{x} → Tm (suc x) → Tm x
  _∘_ : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)


module Demo where
  K : Tm 0
  K = 𝜆 𝜆 𝑣 1

  K′ : Tm 1
  K′ = 𝜆 𝑣 1

  S : Tm 0
  S = 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)


data Ty : Set where
  _⊃_ : Ty → Ty → Ty
  ⊥ : Ty


⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥


data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx


_„_ : Cx → Cx → Cx
Γ „ ∅       = Γ
Γ „ (Δ , A) = Γ „ Δ , A


data _∈[_]_ : Ty → ℕ → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈[ zero ] (Γ , A)

  𝐒_ : ∀{A B x Γ}
      → A ∈[ x ] Γ
      → A ∈[ suc x ] (Γ , B)


data _⊢_∷_ (Γ : Cx) : ∀{x} → Tm x → Ty → Set where
  𝒗_ : ∀{i A}
      → A ∈[ i ] Γ
      → Γ ⊢ 𝑣 i ∷ A

  𝝀_ : ∀{x} {t : Tm (suc x)} {A B}
      → Γ , A ⊢ t ∷ B
      → Γ ⊢ 𝜆 t ∷ (A ⊃ B)

  _∙_ : ∀{x y} {t : Tm x} {s : Tm y} {A B}
      → Γ ⊢ t ∷ (A ⊃ B)    → Γ ⊢ s ∷ A
      → Γ ⊢ t ∘ s ∷ B


⊩_∷_  : ∀{x} → Tm x → Ty → Set
⊩ t ∷ A = ∀{Γ} → Γ ⊢ t ∷ A


𝟎 : ∀{A Γ}
    → A ∈[ 0 ] (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{A B Γ}
    → A ∈[ 1 ] (Γ , A , B)
𝟏 = 𝐒 𝟎

𝟐 : ∀{A B C Γ}
    → A ∈[ 2 ] (Γ , A , B , C)
𝟐 = 𝐒 𝟏


I : ∀{A}
    → ⊩ 𝜆 𝑣 0 ∷ A ⊃ A
I = 𝝀 𝒗 𝟎

K : ∀{A B}
    → ⊩ 𝜆 𝜆 𝑣 1 ∷ A ⊃ B ⊃ A
K = 𝝀 𝝀 𝒗 𝟏

K′ : ∀{A B Γ}
    → Γ , A ⊢ 𝜆 𝑣 1 ∷ B ⊃ A
K′ = 𝝀 𝒗 𝟏

S : ∀{A B C}
    → ⊩ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0) ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)
