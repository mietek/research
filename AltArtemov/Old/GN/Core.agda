module AltArtemov.Old.GN.Core where

open import AltArtemov.Old.GN.Tm public


data Ty : ℕ → Set where
  ⊥  : ∀ {n} → Ty n
  _⊃_ : ∀ {n} → Ty n → Ty n → Ty n
  _∧_ : ∀ {n} → Ty n → Ty n → Ty n
  _∶_ : ∀ {n} → Tm 0 n → Ty n → Ty (suc n)

infixr 5 _⊃_
infixr 15 _∶_


data Cx : Set where
  ∅ : Cx
  _,_ : ∀ {n} → Cx → Ty n → Cx

ᵍ⌊_⌋ : Cx → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋


data _⊇_ : Cx → Cx → Set where
  base : ∅ ⊇ ∅
  weak : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

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

⊇wk : ∀ {Γ n} {A : Ty n} → (Γ , A) ⊇ Γ
⊇wk = weak ⊇id

⊇str : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ (Γ , A) → Γ′ ⊇ Γ
⊇str (weak η) = weak (⊇str η)
⊇str (lift η) = weak η

⊇drop : ∀ {Γ Γ′ n} {A : Ty n} → (Γ′ , A) ⊇ (Γ , A) → Γ′ ⊇ Γ
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

ren-tm-⌊⌋-id : ∀ {Γ n} (t : Tm ᵍ⌊ Γ ⌋ n) → ren-tm ʰ⌊ ⊇id ⌋ t ≡ t
ren-tm-⌊⌋-id {Γ} t rewrite id-⌊⌋-id Γ = ren-tm-id t


data Var : ∀ {n} → Cx → Ty n → Set where
  top : ∀ {Γ n} {A : Ty n} → Var (Γ , A) A
  pop : ∀ {Γ n n′} {A : Ty n} {B : Ty n′} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ n} {A : Ty n} → Var Γ A → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋

ren-var : ∀ {Γ Γ′ n} {A : Ty n} → Γ′ ⊇ Γ → Var Γ A → Var Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {Γ n n′} {A : Ty n} {C : Ty n′} → Var Γ C → Var (Γ , A) C
wk-var = ren-var ⊇wk

wk*-var : ∀ {Γ n} {C : Ty n} → Var ∅ C → Var Γ C
wk*-var ()

ren-var-id : ∀ {Γ n} {A : Ty n} (x : Var Γ A) → ren-var ⊇id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-● : ∀ {Γ Γ′ Γ″ n} {A : Ty n} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (x : Var Γ A) →
              ren-var η′ (ren-var η x) ≡ ren-var (η′ ● η) x
ren-var-● base      η        x       = refl
ren-var-● (weak η′) η        x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (weak η) x       = cong pop (ren-var-● η′ η x)
ren-var-● (lift η′) (lift η) top     = refl
ren-var-● (lift η′) (lift η) (pop x) = cong pop (ren-var-● η′ η x)

ren-fin-⌊⌋-var : ∀ {Γ Γ′ n} {A : Ty n} (η : Γ′ ⊇ Γ) (x : Var Γ A) →
                   ren-fin ʰ⌊ η ⌋ ⁱ⌊ x ⌋ ≡ ⁱ⌊ ren-var η x ⌋
ren-fin-⌊⌋-var base     x       = refl
ren-fin-⌊⌋-var (weak η) x       = cong suc (ren-fin-⌊⌋-var η x)
ren-fin-⌊⌋-var (lift η) top     = refl
ren-fin-⌊⌋-var (lift η) (pop x) = cong suc (ren-fin-⌊⌋-var η x)

x₀ : ∀ {Γ n} {A : Ty n} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ n n′} {A : Ty n} {B : Ty n′} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ n n′ n″} {A : Ty n} {B : Ty n′} {C : Ty n″} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁
