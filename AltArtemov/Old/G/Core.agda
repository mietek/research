module AltArtemov.Old.G.Core where

open import AltArtemov.Old.G.Tm public


data Ty : Set where
  ⊥  : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  _∶_ : Tm 0 → Ty → Ty

infixr 5 _⊃_
infixr 15 _∶_


data Cx : Set where
  ∅ : Cx
  _,_ : Cx → Ty → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋


data _⊇_ : Cx → Cx → Set where
  base : ∅ ⊇ ∅
  weak : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

ʰ⌊_⌋ : ∀ {Γ Γ′} → Γ′ ⊇ Γ → ᵍ⌊ Γ′ ⌋ ≥ ᵍ⌊ Γ ⌋
ʰ⌊ base ⌋   = base
ʰ⌊ weak η ⌋ = weak ʰ⌊ η ⌋
ʰ⌊ lift η ⌋ = lift ʰ⌊ η ⌋

⊇id : ∀ {Γ} → Γ ⊇ Γ
⊇id {∅}     = base
⊇id {Γ , A} = lift ⊇id

⊇to : ∀ {Γ} → Γ ⊇ ∅
⊇to {∅}     = base
⊇to {Γ , A} = weak ⊇to

⊇wk : ∀ {Γ A} → (Γ , A) ⊇ Γ
⊇wk = weak ⊇id

⊇str : ∀ {Γ Γ′ A} → Γ′ ⊇ (Γ , A) → Γ′ ⊇ Γ
⊇str (weak η) = weak (⊇str η)
⊇str (lift η) = weak η

⊇drop : ∀ {Γ Γ′ A} → (Γ′ , A) ⊇ (Γ , A) → Γ′ ⊇ Γ
⊇drop (weak η) = ⊇str η
⊇drop (lift η) = η

_●_ : ∀ {Γ Γ′ Γ″} → Γ″ ⊇ Γ′ → Γ′ ⊇ Γ → Γ″ ⊇ Γ
base    ● η      = η
weak η′ ● η      = weak (η′ ● η)
lift η′ ● weak η = weak (η′ ● η)
lift η′ ● lift η = lift (η′ ● η)

η●id : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → η ● ⊇id ≡ η
η●id base     = refl
η●id (weak η) = cong weak (η●id η)
η●id (lift η) = cong lift (η●id η)

id●η : ∀ {Γ Γ′} (η : Γ′ ⊇ Γ) → ⊇id ● η ≡ η
id●η base     = refl
id●η (weak η) = cong weak (id●η η)
id●η (lift η) = cong lift (id●η η)

id-⌊⌋-id : ∀ Γ → ʰ⌊ ⊇id {Γ} ⌋ ≡ ≥id {ᵍ⌊ Γ ⌋}
id-⌊⌋-id ∅       = refl
id-⌊⌋-id (Γ , A) = cong lift (id-⌊⌋-id Γ)

to-⌊⌋-to : ∀ Γ → ʰ⌊ ⊇to {Γ} ⌋ ≡ ≥to {ᵍ⌊ Γ ⌋}
to-⌊⌋-to ∅       = refl
to-⌊⌋-to (Γ , A) = cong weak (to-⌊⌋-to Γ)

ren-fin-⌊⌋-id : ∀ {Γ} (i : Fin ᵍ⌊ Γ ⌋) → ren-fin ʰ⌊ ⊇id ⌋ i ≡ i
ren-fin-⌊⌋-id {Γ} i rewrite id-⌊⌋-id Γ = ren-fin-id i

ren-tm-⌊⌋-id : ∀ {Γ} (t : Tm ᵍ⌊ Γ ⌋) → ren-tm ʰ⌊ ⊇id ⌋ t ≡ t
ren-tm-⌊⌋-id {Γ} t rewrite id-⌊⌋-id Γ = ren-tm-id t


data Var : Cx → Ty → Set where
  top : ∀ {Γ A} → Var (Γ , A) A
  pop : ∀ {Γ A B} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ A} → Var Γ A → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋

ren-var : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Var Γ A → Var Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {Γ A C} → Var Γ C → Var (Γ , A) C
wk-var = ren-var ⊇wk

wk*-var : ∀ {Γ C} → Var ∅ C → Var Γ C
wk*-var ()

ren-var-id : ∀ {Γ A} (x : Var Γ A) → ren-var ⊇id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-● : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (x : Var Γ A) →
              ren-var η′ (ren-var η x) ≡ ren-var (η′ ● η) x
ren-var-● base      η        x       = refl
ren-var-● (weak η′) η        x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (weak η) x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (lift η) top     = refl
ren-var-● (lift η′) (lift η) (pop x) = cong pop (ren-var-● η′ η x)

ren-fin-⌊⌋-var : ∀ {Γ Γ′ A} (η : Γ′ ⊇ Γ) (x : Var Γ A) →
                   ren-fin ʰ⌊ η ⌋ ⁱ⌊ x ⌋ ≡ ⁱ⌊ ren-var η x ⌋
ren-fin-⌊⌋-var base     x       = refl
ren-fin-⌊⌋-var (weak η) x       = cong suc (ren-fin-⌊⌋-var η x)
ren-fin-⌊⌋-var (lift η) top     = refl
ren-fin-⌊⌋-var (lift η) (pop x) = cong suc (ren-fin-⌊⌋-var η x)

x₀ : ∀ {Γ A} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ A B} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ A B C} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁
