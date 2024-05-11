module A201606.Common.OrderPreservingEmbedding where

open import A201606.Common.Context public

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)


-- Order-preserving embeddings (OPEs).

module _ {𝕌 : Set} where
  infix 1 _⊆_
  data _⊆_ : Cx 𝕌 → Cx 𝕌 → Set where
    done : ∅ ⊆ ∅
    skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {∅}     = done
  refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ η        done      = η
  trans⊆ η        (skip η′) = skip (trans⊆ η η′)
  trans⊆ (skip η) (keep η′) = skip (trans⊆ η η′)
  trans⊆ (keep η) (keep η′) = keep (trans⊆ η η′)

  zero⊆ : ∀ {Γ} → ∅ ⊆ Γ
  zero⊆ {∅}     = done
  zero⊆ {Γ , A} = skip zero⊆

  drop⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ → Γ ⊆ Γ′
  drop⊆ (skip η) = skip (drop⊆ η)
  drop⊆ (keep η) = skip η

  keep⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ , A → Γ ⊆ Γ′
  keep⊆ (skip η) = drop⊆ η
  keep⊆ (keep η) = η

  syntax trans⊆ η η′ = η′ • η

  id₁• : ∀ {Γ Γ′} → (η : Γ ⊆ Γ′) → η • refl⊆ ≡ η
  id₁• done     = refl
  id₁• (skip η) = cong skip (id₁• η)
  id₁• (keep η) = cong keep (id₁• η)

  id₂• : ∀ {Γ Γ′} → (η : Γ ⊆ Γ′) → refl⊆ • η ≡ η
  id₂• done     = refl
  id₂• (skip η) = cong skip (id₂• η)
  id₂• (keep η) = cong keep (id₂• η)

  assoc• : ∀ {Γ Γ′ Γ″ Γ‴} → (η : Γ ⊆ Γ′) (η′ : Γ′ ⊆ Γ″) (η″ : Γ″ ⊆ Γ‴) → (η″ • η′) • η ≡ η″ • (η′ • η)
  assoc• η        η′        done      = refl
  assoc• η        η′        (skip η″) = cong skip (assoc• η η′ η″)
  assoc• η        (skip η′) (keep η″) = cong skip (assoc• η η′ η″)
  assoc• (skip η) (keep η′) (keep η″) = cong skip (assoc• η η′ η″)
  assoc• (keep η) (keep η′) (keep η″) = cong keep (assoc• η η′ η″)

  ren-var : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Renᵢ Γ Γ′
  ren-var done     ()
  ren-var (skip η) i       = pop (ren-var η i)
  ren-var (keep η) top     = top
  ren-var (keep η) (pop i) = pop (ren-var η i)

  ren-var-refl⊆ : ∀ {A Γ} → (i : A ∈ Γ) → ren-var refl⊆ i ≡ i
  ren-var-refl⊆ top     = refl
  ren-var-refl⊆ (pop i) = cong pop (ren-var-refl⊆ i)

  ren-var-trans⊆ : ∀ {A Γ Γ′ Γ″} → (η : Γ ⊆ Γ′) (η′ : Γ′ ⊆ Γ″) (i : A ∈ Γ) → ren-var η′ (ren-var η i) ≡ ren-var (η′ • η) i
  ren-var-trans⊆ done     η′        ()
  ren-var-trans⊆ η        (skip η′) i       = cong pop (ren-var-trans⊆ η η′ i)
  ren-var-trans⊆ (skip η) (keep η′) i       = cong pop (ren-var-trans⊆ η η′ i)
  ren-var-trans⊆ (keep η) (keep η′) top     = refl
  ren-var-trans⊆ (keep η) (keep η′) (pop i) = cong pop (ren-var-trans⊆ η η′ i)
