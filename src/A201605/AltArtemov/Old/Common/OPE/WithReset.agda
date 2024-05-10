module A201605.AltArtemov.Old.Common.OPE.WithReset where

open import A201605.AltArtemov.Old.Common.Vec.Basic public
open import A201605.AltArtemov.Old.Common.Cx.WithReset public


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

°id : ∀ Γ → ʰ⌊ ⊇id {Γ} ⌋ ≡ ≥id {ᵍ⌊ Γ ⌋}
°id ∅       = refl
°id (Γ , A) = cong lift (°id Γ)

°to : ∀ Γ → ʰ⌊ ⊇to {Γ} ⌋ ≡ ≥to {ᵍ⌊ Γ ⌋}
°to ∅       = refl
°to (Γ , A) = cong weak (°to Γ)

°ren-fin-id : ∀ {Γ} (i : Fin ᵍ⌊ Γ ⌋) → ren-fin ʰ⌊ ⊇id ⌋ i ≡ i
°ren-fin-id {Γ} rewrite °id Γ = ren-fin-id

°ren-tm-id : ∀ {Γ n} (t : Tm ᵍ⌊ Γ ⌋ n) → ren-tm ʰ⌊ ⊇id ⌋ t ≡ t
°ren-tm-id {Γ} rewrite °id Γ = ren-tm-id

°ren-vec-id : ∀ {Γ k n} (ts : Vec ᵍ⌊ Γ ⌋ k n) → ren-vec ʰ⌊ ⊇id ⌋ ts ≡ ts
°ren-vec-id {Γ} rewrite °id Γ = ren-vec-id
