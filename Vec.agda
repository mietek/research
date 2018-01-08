module Vec where

open import Prelude
open import Fin


--------------------------------------------------------------------------------


data Vec (X : Set) : Nat → Set
  where
    ∙   : Vec X zero
    _,_ : ∀ {n} → Vec X n → X → Vec X (suc n)


map : ∀ {X Y n} → (X → Y) → Vec X n
                → Vec Y n
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A


module GetVec
  where
    get : ∀ {X n} → Vec X n → Fin n
                  → X
    get (Ξ , A) zero    = A
    get (Ξ , B) (suc i) = get Ξ i


    gets : ∀ {X n n′} → Vec X n′ → n′ ≥ n
                      → Vec X n
    gets Ξ       done     = ∙
    gets (Ξ , B) (drop e) = gets Ξ e
    gets (Ξ , A) (keep e) = gets Ξ e , A


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
              → Ξ ⊇⟨ id≥ ⟩ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇


_∘⊇_ : ∀ {X n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                           → Ξ′ ⊇⟨ e₁ ⟩ Ξ → Ξ″ ⊇⟨ e₂ ⟩ Ξ′
                           → Ξ″ ⊇⟨ e₁ ∘≥ e₂ ⟩ Ξ
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


ren∋ : ∀ {X A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ → Ξ ∋⟨ i ⟩ A
                        → Ξ′ ∋⟨ renF e i ⟩ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)


--------------------------------------------------------------------------------
