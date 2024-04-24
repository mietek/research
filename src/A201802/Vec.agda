module A201802.Vec where

open import A201802.Prelude
open import A201802.Category
open import A201802.Fin
open import A201802.FinLemmas


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


inj,₁ : ∀ {X n A₁ A₂} → {Ξ₁ Ξ₂ : Vec X n}
                      → Ξ₁ Vec., A₁ ≡ Ξ₂ , A₂
                      → Ξ₁ ≡ Ξ₂
inj,₁ refl = refl


inj,₂ : ∀ {X n A₁ A₂} → {Ξ₁ Ξ₂ : Vec X n}
                      → Ξ₁ Vec., A₁ ≡ Ξ₂ , A₂
                      → A₁ ≡ A₂
inj,₂ refl = refl


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


bot⊇ : ∀ {X n} → {Ξ : Vec X n}
               → Ξ ⊇⟨ bot≥ ⟩ ∙
bot⊇ {Ξ = ∙}     = done
bot⊇ {Ξ = Ξ , A} = drop bot⊇


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
    zero : ∀ {n A} → {Ξ : Vec X n}
                   → Ξ , A ∋⟨ zero ⟩ A

    suc : ∀ {B n i A} → {Ξ : Vec X n}
                      → Ξ ∋⟨ i ⟩ A
                      → Ξ , B ∋⟨ suc i ⟩ A


ren∋ : ∀ {X A n n′ e I} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ → Ξ ∋⟨ I ⟩ A
                        → Ξ′ ∋⟨ REN∋ e I ⟩ A
ren∋ done     i       = i
ren∋ (drop η) i       = suc (ren∋ η i)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc i) = suc (ren∋ η i)


get∋ : ∀ {X n} → {Ξ : Vec X n} {I : Fin n}
               → Ξ ∋⟨ I ⟩ GET Ξ I
get∋ {Ξ = Ξ , A} {zero}  = zero
get∋ {Ξ = Ξ , B} {suc I} = suc get∋


uniq∋ : ∀ {X n I A₁ A₂} → {Ξ : Vec X n}
                        → (i₁ : Ξ ∋⟨ I ⟩ A₁) (i₂ : Ξ ∋⟨ I ⟩ A₂)
                        → A₁ ≡ A₂
uniq∋ zero     zero     = refl
uniq∋ (suc i₁) (suc i₂) = uniq∋ i₁ i₂


--------------------------------------------------------------------------------


zip : ∀ {X Y n} → Vec X n → Vec Y n
                → Vec (X × Y) n
zip ∙         ∙         = ∙
zip (Ξ₁ , A₁) (Ξ₂ , A₂) = zip Ξ₁ Ξ₂ , (A₁ , A₂)


zip∋₁ : ∀ {X Y n I A₁} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₁ ∋⟨ I ⟩ A₁
                       → zip Ξ₁ Ξ₂ ∋⟨ I ⟩ (A₁ , GET Ξ₂ I)
zip∋₁ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₁ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc i) = suc (zip∋₁ i)

zip∋₂ : ∀ {X Y n I A₂} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₂ ∋⟨ I ⟩ A₂
                       → zip Ξ₁ Ξ₂ ∋⟨ I ⟩ (GET Ξ₁ I , A₂)
zip∋₂ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₂ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc i) = suc (zip∋₂ i)


within : ∀ {X Y n I A} → {Ξ : Vec X n}
                       → (Ψ : Vec Y n) → Ξ ∋⟨ I ⟩ A
                       → Ψ ∋⟨ I ⟩ GET Ψ I
within (Ψ , B) zero    = zero
within (Ψ , C) (suc i) = suc (within Ψ i)


--------------------------------------------------------------------------------
