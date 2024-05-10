module AltArtemov.Old.Common.Var.WithG where

open import AltArtemov.Old.Common.OPE.WithG public


data Var : ∀ {n} → Cx → Ty 0 n → Set where
  top : ∀ {Γ n} {A : Ty 0 n} → Var (Γ , A) A
  pop : ∀ {Γ n n′} {A : Ty 0 n} {B : Ty 0 n′} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ n} {A : Ty 0 n} → Var Γ A → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋

ren-var : ∀ {Γ Γ′ n} {A : Ty 0 n} → Γ′ ⊇ Γ → Var Γ A → Var Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {Γ n n′} {A : Ty 0 n} {C : Ty 0 n′} → Var Γ C → Var (Γ , A) C
wk-var = ren-var ⊇wk

wk*-var : ∀ {Γ n} {C : Ty 0 n} → Var ∅ C → Var Γ C
wk*-var ()

ren-var-id : ∀ {Γ n} {A : Ty 0 n} (x : Var Γ A) → ren-var ⊇id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-● : ∀ {Γ Γ′ Γ″ n} {A : Ty 0 n} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (x : Var Γ A) →
              ren-var η′ (ren-var η x) ≡ ren-var (η′ ● η) x
ren-var-● base      η        x       = refl
ren-var-● (weak η′) η        x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (weak η) x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (lift η) top     = refl
ren-var-● (lift η′) (lift η) (pop x) = cong pop (ren-var-● η′ η x)

°ren-fin-var : ∀ {Γ Γ′ n} {A : Ty 0 n} (η : Γ′ ⊇ Γ) (x : Var Γ A) →
                 ren-fin ʰ⌊ η ⌋ ⁱ⌊ x ⌋ ≡ ⁱ⌊ ren-var η x ⌋
°ren-fin-var base     x       = refl
°ren-fin-var (weak η) x       = cong suc (°ren-fin-var η x)
°ren-fin-var (lift η) top     = refl
°ren-fin-var (lift η) (pop x) = cong suc (°ren-fin-var η x)

x₀ : ∀ {Γ n} {A : Ty 0 n} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ n n′} {A : Ty 0 n} {B : Ty 0 n′} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ n n′ n″} {A : Ty 0 n} {B : Ty 0 n′} {C : Ty 0 n″} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁
