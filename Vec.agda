module Vec where

open import Prelude
open import Category
open import Fin
open import FinLemmas


--------------------------------------------------------------------------------


data Vec (X : Set) : Nat → Set
  where
    ∙   : Vec X zero
    _,_ : ∀ {n} → Vec X n → X → Vec X (suc n)


MAPS : ∀ {X Y n} → (X → Y) → Vec X n
                 → Vec Y n
MAPS F ∙       = ∙
MAPS F (Ξ , A) = MAPS F Ξ , F A


--------------------------------------------------------------------------------


GET : ∀ {X n} → Vec X n → Fin n
              → X
GET (Ξ , A) zero    = A
GET (Ξ , B) (suc i) = GET Ξ i


GETS : ∀ {X n n′} → Vec X n′ → n′ ≥ n
                  → Vec X n
GETS Ξ       done     = ∙
GETS (Ξ , B) (drop e) = GETS Ξ e
GETS (Ξ , A) (keep e) = GETS Ξ e , A


--------------------------------------------------------------------------------


infix 4 _⊇⟨_⟩_
data _⊇⟨_⟩_ {X} : ∀ {n n′} → Vec X n′ → n′ ≥ n → Vec X n → Set
  where
    done : ∙ ⊇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ drop e ⟩ Ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ keep e ⟩ Ξ , A


id⊇ : ∀ {X n} → {Ξ : Vec X n}
              → Ξ ⊇⟨ id ⟩ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇


_∘⊇_ : ∀ {X n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                           → Ξ′ ⊇⟨ e₁ ⟩ Ξ → Ξ″ ⊇⟨ e₂ ⟩ Ξ′
                           → Ξ″ ⊇⟨ e₁ ∘ e₂ ⟩ Ξ
η₁      ∘⊇ done    = η₁
η₁      ∘⊇ drop η₂ = drop (η₁ ∘⊇ η₂)
drop η₁ ∘⊇ keep η₂ = drop (η₁ ∘⊇ η₂)
keep η₁ ∘⊇ keep η₂ = keep (η₁ ∘⊇ η₂)


--------------------------------------------------------------------------------


infix 4 _∋⟨_⟩_
data _∋⟨_⟩_ {X} : ∀ {n} → Vec X n → Fin n → X → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n}
                   → Ξ , A ∋⟨ zero ⟩ A

    suc : ∀ {B A n i} → {Ξ : Vec X n}
                      → Ξ ∋⟨ i ⟩ A
                      → Ξ , B ∋⟨ suc i ⟩ A


get∋ : ∀ {X n} → {Ξ : Vec X n} {I : Fin n}
               → Ξ ∋⟨ I ⟩ GET Ξ I
get∋ {Ξ = Ξ , A} {zero}  = zero
get∋ {Ξ = Ξ , B} {suc I} = suc get∋


ren∋ : ∀ {X A n n′ e I} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ → Ξ ∋⟨ I ⟩ A
                        → Ξ′ ∋⟨ REN∋ e I ⟩ A
ren∋ done     i       = i
ren∋ (drop η) i       = suc (ren∋ η i)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc i) = suc (ren∋ η i)


--------------------------------------------------------------------------------
