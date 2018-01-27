module LPTTTypes where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import S4TTTerms
open import S4TTTermsLemmas


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Type : Nat → Set
  where
    ι_   : ∀ {d} → String → Type d
    _⊃_  : ∀ {d} → Type d → Type d → Type d
    [_]_ : ∀ {d} → Term d zero → Type d → Type d


instance
  TypeVar : ∀ {d} → IsString (Type d)
  TypeVar =
    record
      { Constraint = \ s → ⊤
      ; fromString = \ s → ι s
      }


Types : Nat → Nat → Set
Types d g = Vec (Type d) g


--------------------------------------------------------------------------------


MRENₚ : ∀ {d d′} → d′ ≥ d → Type d
                 → Type d′
MRENₚ e (ι P)     = ι P
MRENₚ e (A ⊃ B)   = MRENₚ e A ⊃ MRENₚ e B
MRENₚ e ([ M ] A) = [ MREN e M ] MRENₚ e A


MWKₚ : ∀ {d} → Type d
             → Type (suc d)
MWKₚ A = MRENₚ (drop id≥) A


MSUBₚ : ∀ {d n} → Terms* d n → Type n
                → Type d
MSUBₚ τ (ι P)     = ι P
MSUBₚ τ (A ⊃ B)   = MSUBₚ τ A ⊃ MSUBₚ τ B
MSUBₚ τ ([ M ] A) = [ MSUB τ M ] MSUBₚ τ A


MCUTₚ : ∀ {d} → Term d zero → Type (suc d)
              → Type d
MCUTₚ M A = MSUBₚ (MIDS* , M) A


--------------------------------------------------------------------------------


record Assert (d : Nat) : Set
  where
    constructor ⟪⊫_⦂_⟫
    field
      M : Term d zero
      A : Type d


data Asserts : Nat → Set
  where
    ∙ : Asserts zero

    _,_ : ∀ {d} → Asserts d → Assert d
                → Asserts (suc d)


--------------------------------------------------------------------------------


infix 4 _⊇◆⟨_⟩_
data _⊇◆⟨_⟩_ : ∀ {d d′} → Asserts d′ → d′ ≥ d → Asserts d → Set
  where
    done : ∙ ⊇◆⟨ done ⟩ ∙

    drop : ∀ {d d′ e} → {Δ : Asserts d} {Δ′ : Asserts d′} {M : Term d′ zero} {A : Type d′}
                      → Δ′ ⊇◆⟨ e ⟩ Δ
                      → Δ′ , ⟪⊫ M ⦂ A ⟫ ⊇◆⟨ drop e ⟩ Δ

    keep : ∀ {d d′ e} → {Δ : Asserts d} {Δ′ : Asserts d′} {M : Term d zero} {A : Type d}
                         {M′ : Term d′ zero} {{p : MREN e M ≡ M′}}
                         {A′ : Type d′} {{q : MRENₚ e A ≡ A′}}
                      → Δ′ ⊇◆⟨ e ⟩ Δ
                      → Δ′ , ⟪⊫ M′ ⦂ A′ ⟫ ⊇◆⟨ keep e ⟩ Δ , ⟪⊫ M ⦂ A ⟫


id⊇◆ : ∀ {d} → {Δ : Asserts d}
             → Δ ⊇◆⟨ id ⟩ Δ
id⊇◆ {Δ = ∙}               = done
id⊇◆ {Δ = Δ , ⟪⊫ M ⦂ A ⟫} = keep {{id-MREN M}} {{{!id-MRENₚ A!}}} id⊇◆
