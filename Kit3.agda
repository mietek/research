module Kit3 where

open import Isomorphism public
open import Kit1 public


----------------------------------------------------------------------------------------------------

record RedKit1! : Set₁ where
  constructor redkit1
  field
    tk! : TmKit!
  open TmKit! tk! public
  open TmKit tk! public
  field
    _⇒_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set

module RedKit1 (rk1! : RedKit1!) (open RedKit1! rk1!) where
  -- reducible forms
  RF : ∀ {Γ A} → Γ ⊢ A → Set
  RF t = Σ _ λ t′ → t ⇒ t′

  -- irreducible forms
  ¬R : ∀ {Γ A} → Γ ⊢ A → Set
  ¬R t = ∀ {t′} → ¬ t ⇒ t′

  -- iterated reduction
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
    begin_ rs = rs

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

  module _ (⚠ : Extensionality) where
    uni¬RF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ RF t) → ¬p ≡ ¬p′
    uni¬RF = uni→ ⚠ uni𝟘


----------------------------------------------------------------------------------------------------

record RedKit2! : Set₁ where
  constructor redkit2
  field
    rk1! : RedKit1!
  open RedKit1! rk1! public
  open RedKit1 rk1! public
  field
    {NF}   : ∀ {Γ A} → Γ ⊢ A → Set
    uniNF  : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
    NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t

module RedKit2 (rk2! : RedKit2!) (open RedKit2! rk2!) where
  ¬RF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → ¬R t
  ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

  ¬R→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → ¬ RF t
  ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

  RF→¬NF : ∀ {Γ A} {t : Γ ⊢ A} → RF t → ¬ NF t
  RF→¬NF (_ , r) p = r ↯ NF→¬R p

  NF→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬ RF t
  NF→¬RF = ¬R→¬RF ∘ NF→¬R

  data Prog {Γ A} (t : Γ ⊢ A) : Set where
    done : NF t → Prog t
    step : ∀ {t′ : Γ ⊢ A} → t ⇒ t′ → Prog t
  -- NOTE: the above `step` is slightly more convenient than but equivalent to the below `step`
  -- step : Σ (Γ ⊢ A) (λ t′ → t ⇒ t′) → Prog t

  recProg : ∀ {𝓍} {X : Set 𝓍} {Γ A} {t : Γ ⊢ A} → Prog t → (NF t → X) → (RF t → X) → X
  recProg (done p) f₁ f₂ = f₁ p
  recProg (step r) f₁ f₂ = f₂ (_ , r)


----------------------------------------------------------------------------------------------------

record DetKit! : Set₁ where
  constructor detkit
  field
    rk2! : RedKit2!
  open RedKit2! rk2! public
  open RedKit2 rk2! public
  field
    det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
    uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′

module DetKit (dk! : DetKit!) (open DetKit! dk!) where
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

record ProgKit! : Set₁ where
  constructor progkit
  field
    rk2! : RedKit2!
  open RedKit2! rk2! public
  open RedKit2 rk2! public
  field
    prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t

module ProgKit (pk! : ProgKit!) (open ProgKit! pk!) where
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

  module _ (⚠ : Extensionality) where
    NF≃¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t ≃ (¬ RF t)
    NF≃¬RF = record
      { to      = NF→¬RF
      ; from    = ¬RF→NF
      ; from∘to = λ p → uniNF ((¬RF→NF ∘ NF→¬RF) p) p
      ; to∘from = λ p → uni¬RF ⚠ ((NF→¬RF ∘ ¬RF→NF) p) p
      }


----------------------------------------------------------------------------------------------------

record NF?→ProgKit! : Set₁ where
  constructor nf?→progkit
  field
    rk2! : RedKit2!
  open RedKit2! rk2! public
  open RedKit2 rk2! public
  field
    NF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
    ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t

module NF?→ProgKit (nfpk! : NF?→ProgKit!) (open NF?→ProgKit! nfpk!) where
  prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
  prog⇒ t    with NF? t
  ... | yes p   = done p
  ... | no ¬p   = let _ , r = ¬NF→RF ¬p
                    in step r

  pk! = progkit rk2! prog⇒
  open ProgKit pk! public hiding (NF? ; ¬NF→RF)


----------------------------------------------------------------------------------------------------

record RF?→ProgKit! : Set₁ where
  constructor rf?→progkit
  field
    rk2! : RedKit2!
  open RedKit2! rk2! public
  open RedKit2 rk2! public
  field
    RF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
    ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t

module RF?→ProgKit (rfpk! : RF?→ProgKit!) (open RF?→ProgKit! rfpk!) where
  prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
  prog⇒ t          with RF? t
  ... | yes (_ , r)   = step r
  ... | no ¬p         = done (¬RF→NF ¬p)

  pk! = progkit rk2! prog⇒
  open ProgKit pk! public hiding (RF? ; ¬RF→NF)


----------------------------------------------------------------------------------------------------
