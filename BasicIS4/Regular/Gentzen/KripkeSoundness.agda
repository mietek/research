module BasicIS4.Regular.Gentzen.KripkeSoundness where

open import BasicIS4.Regular.Gentzen public


module Ono where
  open import BasicIS4.KripkeSemantics.Ono public

  --   w′  R  v′
  --   ●──────●
  --   │     ⋰
  -- ≤ │   R
  --   │ ⋰
  --   ●
  --   w
  --
  -- zigR : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → w R v′

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} {{_ : Model}} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)


module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public

  --   w′  R  v′
  --   ●──────●
  --   │      ┊
  -- ≤ │      ┊ ≤
  --   │      ┊
  --   ●╌╌╌╌╌╌◌
  --   w   R  v
  --
  -- zigzagR⨾≤ : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → ∃ (λ v → w R v × v ≤ v′)

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → eval u (eval⋆ ts γ ζ)
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} {{_ : Model}} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {v′} → w R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ζ = eval⋆ ts γ ζ , λ ζ′ → eval t γ (transR ζ ζ′)


module Wijesekera where
  open import BasicIS4.KripkeSemantics.Wijesekera public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} {{_ : Model}} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
      let _ , (ξ″ , ζ″) = zigzag≤⨾R ξ′ ζ
      in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)


module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public

  -- zap            zagzig
  --   w′  R  v′      w′  R  v′
  --   ●╌╌╌╌╌╌◌       ◌╌╌╌╌╌╌●
  --   │      ┊       ┊      │
  -- ≤ │      ┊ ≤   ≤ ┊      │ ≤
  --   │      ┊       ┊      │
  --   ●──────●       ●──────●
  --   w   R  v       w   R  v
  --
  -- zap       : ∀ {v w w′} → w R v → w ≤ w′ → ∃ (λ v′ → w′ R v′ × v ≤ v′)
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} {{_ : Model}} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
      let _ , (ξ″ , ζ″) = zagzig≤⨾R ξ′ ζ
      in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)


module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public

  --   w′  R  v′
  --   ◌╌╌╌╌╌╌●
  --   ┊      │
  -- ≤ ┊      │ ≤
  --   ┊      │
  --   ●──────●
  --   w   R  v
  --
  -- zagzig≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → eval u (eval⋆ ts γ ξ ζ)
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} {{_ : Model}} {w : World}
            → Γ ⊢⋆ □⋆ Δ → w ⊩⋆ Γ → ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ □⋆ Δ
    eval⋆ {⌀}     ∙        γ ξ ζ = ∙
    eval⋆ {Δ , B} (ts , t) γ ξ ζ = eval⋆ ts γ ξ ζ , λ ξ′ ζ′ →
      let _ , (ξ″ , ζ″) = zagzig≤⨾R ξ′ ζ
      in  eval t γ (trans≤ ξ ξ″) (transR ζ″ ζ′)
