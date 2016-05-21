module AltArtemov.Try2.Var where

open import AltArtemov.Try2.OPE public


data Var : ∀ {k} → Cx → Ty k → Set where
  top : ∀ {Γ k} {A : Ty k} → Var (Γ , A) A
  pop : ∀ {Γ k k′} {A : Ty k} {B : Ty k′} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ k} {A : Ty k} → Var Γ A → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋

ren-var : ∀ {Γ Γ′ k} {A : Ty k} → Γ′ ⊇ Γ → Var Γ A → Var Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {Γ k k′} {A : Ty k} {C : Ty k′} → Var Γ C → Var (Γ , A) C
wk-var = ren-var ⊇wk

wk*-var : ∀ {Γ k} {C : Ty k} → Var ∅ C → Var Γ C
wk*-var ()

ren-var-id : ∀ {Γ k} {A : Ty k} (x : Var Γ A) → ren-var ⊇id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-● : ∀ {Γ Γ′ Γ″ k} {A : Ty k} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (x : Var Γ A) →
              ren-var η′ (ren-var η x) ≡ ren-var (η′ ● η) x
ren-var-● base      η        x       = refl
ren-var-● (weak η′) η        x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (weak η) x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (lift η) top     = refl
ren-var-● (lift η′) (lift η) (pop x) = cong pop (ren-var-● η′ η x)

°ren-fin-var : ∀ {Γ Γ′ k} {A : Ty k} (η : Γ′ ⊇ Γ) (x : Var Γ A) →
                 ren-fin ʰ⌊ η ⌋ ⁱ⌊ x ⌋ ≡ ⁱ⌊ ren-var η x ⌋
°ren-fin-var base     x       = refl
°ren-fin-var (weak η) x       = cong suc (°ren-fin-var η x)
°ren-fin-var (lift η) top     = refl
°ren-fin-var (lift η) (pop x) = cong suc (°ren-fin-var η x)

x₀ : ∀ {Γ k} {A : Ty k} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ k k′} {A : Ty k} {B : Ty k′} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ k k′ k″} {A : Ty k} {B : Ty k′} {C : Ty k″} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁
