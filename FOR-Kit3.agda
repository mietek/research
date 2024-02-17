module FOR-Kit3 where

open import FOR-Kit1 public


----------------------------------------------------------------------------------------------------

record RedKit1Params : Set₁ where
  constructor kit
  field
    tmkit : TmKitParams
  open TmKitParams tmkit public
  open TmKit tmkit public hiding (tmkit)
  infix 4 _⇒_
  field
    _⇒_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set

module RedKit1 (¶ : RedKit1Params) where
  open RedKit1Params ¶
  redkit1 = ¶

  -- reducible forms
  RF : ∀ {Γ A} → Γ ⊢ A → Set
  RF t = Σ _ λ t′ → t ⇒ t′

  -- irreducible forms
  ¬R : ∀ {Γ A} → Γ ⊢ A → Set
  ¬R t = ∀ {t′} → ¬ t ⇒ t′

  -- multi-step reduction
  -- TODO: switch direction
  infix 4 _⇒*_
  data _⇒*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
    done : ∀ {t} → t ⇒* t
    step : ∀ {t t′ t″} (r : t ⇒ t′) (rs : t′ ⇒* t″) → t ⇒* t″

  trans⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
  trans⇒* done        rs′ = rs′
  trans⇒* (step r rs) rs′ = step r (trans⇒* rs rs′)

  ≡→⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ⇒* t′
  ≡→⇒* refl = done

  module ⇒*-Reasoning where
    infix 1 begin_
    begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → t ⇒* t′
    begin rs = rs

    infixr 2 _⇒*⟨_⟩_
    _⇒*⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
    t ⇒*⟨ rs ⟩ rs′ = trans⇒* rs rs′

    infixr 2 _⇒⟨_⟩_
    _⇒⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒ t′ → t′ ⇒* t″ → t ⇒* t″
    t ⇒⟨ r ⟩ rs = step r rs

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ⇒* t′ → t ⇒* t′
    t ≡⟨⟩ rs = rs

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ⇒* t″ → t ⇒* t″
    t ≡⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* eq) rs′

    infixr 2 _≡˘⟨_⟩_
    _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ⇒* t″ → t ⇒* t″
    t ≡˘⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* (sym eq)) rs′

    infix 3 _∎
    _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ⇒* t
    t ∎ = done


----------------------------------------------------------------------------------------------------

record RedKit2Params : Set₁ where
  constructor kit
  field
    redkit1 : RedKit1Params
  open RedKit1Params redkit1 public
  open RedKit1 redkit1 public hiding (redkit1)
  field
    {NF}   : ∀ {Γ A} → Γ ⊢ A → Set
    uniNF  : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
    NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t

module RedKit2 (¶ : RedKit2Params) where
  open RedKit2Params ¶
  redkit2 = ¶

  ¬RF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → ¬R t
  ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

  ¬R→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → ¬ RF t
  ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

  RF→¬NF : ∀ {Γ A} {t : Γ ⊢ A} → RF t → ¬ NF t
  RF→¬NF (_ , r) p = r ↯ NF→¬R p

  NF→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬ RF t
  NF→¬RF = ¬R→¬RF ∘ NF→¬R

  -- TODO: prove equivalent to `Prog` with `step : RF t → Prog t`
  data Prog {Γ A} (t : Γ ⊢ A) : Set where
    done : NF t → Prog t
    step : ∀ {t′ : Γ ⊢ A} → t ⇒ t′ → Prog t

  recProg : ∀ {𝓍} {X : Set 𝓍} {Γ A} {t : Γ ⊢ A} → Prog t → (NF t → X) → (RF t → X) → X
  recProg (done p) f₁ f₂ = f₁ p
  recProg (step r) f₁ f₂ = f₂ (_ , r)


----------------------------------------------------------------------------------------------------

record DetKitParams : Set₁ where
  constructor kit
  field
    redkit2 : RedKit2Params
  open RedKit2Params redkit2 public
  open RedKit2 redkit2 public hiding (redkit2)
  field
    det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
    uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′

module DetKit (¶ : DetKitParams) where
  open DetKitParams ¶
  detkit = ¶

  skip⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒* t″ → NF t″ → t′ ⇒* t″
  skip⇒* r done          p″ = r ↯ NF→¬R p″
  skip⇒* r (step r′ rs′) p″ with det⇒ r r′
  ... | refl                  = rs′

  uni⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} (rs rs′ : t ⇒* t′) → NF t′ → rs ≡ rs′
  uni⇒* done        done          p′ = refl
  uni⇒* done        (step r′ rs′) p′ = r′ ↯ NF→¬R p′
  uni⇒* (step r rs) done          p′ = r ↯ NF→¬R p′
  uni⇒* (step r rs) (step r′ rs′) p′ with det⇒ r r′
  ... | refl                            = step & uni⇒ r r′ ⊗ uni⇒* rs rs′ p′

  det⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → NF t′ → t ⇒* t″ → NF t″ → t′ ≡ t″
  det⇒* done        p′ done          p″ = refl
  det⇒* done        p′ (step r′ rs′) p″ = r′ ↯ NF→¬R p′
  det⇒* (step r rs) p′ rs′           p″ = det⇒* rs p′ (skip⇒* r rs′ p″) p″

  -- TODO: sort this out using Schäfer
  -- local confluence
  lconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒ t₁ → t ⇒ t₂ →
            Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
  lconf⇒ r r′ with det⇒ r r′
  ... | refl     = _ , done , done

  -- global confluence
  gconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒* t₁ → t ⇒* t₂ →
            Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
  gconf⇒ done        rs′           = _ , rs′ , done
  gconf⇒ (step r rs) done          = _ , done , step r rs
  gconf⇒ (step r rs) (step r′ rs′) with det⇒ r r′
  ... | refl                          = gconf⇒ rs rs′


----------------------------------------------------------------------------------------------------

record ProgKitParams : Set₁ where
  constructor kit
  field
    redkit2 : RedKit2Params
  open RedKit2Params redkit2 public
  open RedKit2 redkit2 public hiding (redkit2)
  field
    prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t

module ProgKit (¶ : ProgKitParams) where
  open ProgKitParams ¶
  progkit = ¶

  NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
  NF? t = recProg (prog⇒ t) yes (no ∘ RF→¬NF)

  RF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
  RF? t = recProg (prog⇒ t) (no ∘ NF→¬RF) yes

  ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
  ¬NF→RF ¬p = recProg (prog⇒ _) (_↯ ¬p) id

  ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
  ¬RF→NF ¬p = recProg (prog⇒ _) id (_↯ ¬p)

  ¬R→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → NF t
  ¬R→NF = ¬RF→NF ∘ ¬R→¬RF


----------------------------------------------------------------------------------------------------

record NF?→ProgKitParams : Set₁ where
  constructor kit
  field
    redkit2 : RedKit2Params
  open RedKit2Params redkit2 public
  open RedKit2 redkit2 public hiding (redkit2)
  field
    NF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
    ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t

module NF?→ProgKit (¶ : NF?→ProgKitParams) where
  open NF?→ProgKitParams ¶
  nf?→progkit = ¶

  prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
  prog⇒ t    with NF? t
  ... | yes p   = done p
  ... | no ¬p   = let _ , r = ¬NF→RF ¬p
                    in step r

  open ProgKit (kit redkit2 prog⇒) public hiding (NF? ; ¬NF→RF)


----------------------------------------------------------------------------------------------------

record RF?→ProgKitParams : Set₁ where
  constructor kit
  field
    redkit2 : RedKit2Params
  open RedKit2Params redkit2 public
  open RedKit2 redkit2 public hiding (redkit2)
  field
    RF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
    ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t

module RF?→ProgKit (¶ : RF?→ProgKitParams) where
  open RF?→ProgKitParams ¶
  rf?→progkit = ¶

  prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
  prog⇒ t          with RF? t
  ... | yes (_ , r)   = step r
  ... | no ¬p         = done (¬RF→NF ¬p)

  open ProgKit (kit redkit2 prog⇒) public hiding (RF? ; ¬RF→NF)


----------------------------------------------------------------------------------------------------
