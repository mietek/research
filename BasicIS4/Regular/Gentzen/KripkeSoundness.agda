module BasicIS4.Regular.Gentzen.KripkeSoundness where

open import BasicIS4.Regular.Gentzen public

import BasicIS4.Regular.Hilbert.KripkeSoundness as KS
import BasicIS4.Regular.Translation as T


-- NOTE: Round-tripping via Hilbert-style soundness is not fully satisfactory.

module Ono where
  open import BasicIS4.KripkeSemantics.Ono

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval = KS.Ono.eval ∘ T.g→hn

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval = KS.BozicDosen.eval ∘ T.g→hn

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval = KS.EwaldEtAl.eval ∘ T.g→hn

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval = KS.AlechinaEtAl.eval ∘ T.g→hn

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- NOTE: For each semantics, □ introduction is the problematic case.

-- module Ono where
--   open import BasicIS4.KripkeSemantics.Ono public

--   --   w′  R  v′
--   --   ●──────●
--   --   │     ⋰
--   -- ≤ │   R
--   --   │ ⋰
--   --   ●
--   --   w
--   --
--   -- switchR : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → w R v′

--   mutual
--     eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
--     eval (var i)         γ = lookup i γ
--     eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
--     eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
--     eval (multibox ts u) γ = λ ζ → {!!}
--     eval (down t)        γ = (eval t γ) reflR
--     eval (pair t u)      γ = eval t γ , eval u γ
--     eval (fst t)         γ = π₁ (eval t γ)
--     eval (snd t)         γ = π₂ (eval t γ)
--     eval tt              γ = ∙

--     eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
--     eval⋆ {⌀}     ∙        γ = ∙
--     eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- module BozicDosen where
--   open import BasicIS4.KripkeSemantics.BozicDosen public

--   --   w′  R  v′
--   --   ●──────●
--   --   │      ┊
--   -- ≤ │      ┊ ≤
--   --   │      ┊
--   --   ●╌╌╌╌╌╌◌
--   --   w   R  v
--   --
--   -- switchR⨾≤ : ∀ {v′ w w′} → w′ R v′ → w ≤ w′ → ∃ (λ v → w R v × v ≤ v′)

--   mutual
--     eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
--     eval (var i)         γ = lookup i γ
--     eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
--     eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
--     eval (multibox ts u) γ = λ ζ → {!!}
--     eval (down t)        γ = (eval t γ) reflR
--     eval (pair t u)      γ = eval t γ , eval u γ
--     eval (fst t)         γ = π₁ (eval t γ)
--     eval (snd t)         γ = π₂ (eval t γ)
--     eval tt              γ = ∙

--     eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
--     eval⋆ {⌀}     ∙        γ = ∙
--     eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- module Wijesekera where
--   open import BasicIS4.KripkeSemantics.Wijesekera public

--   mutual
--     eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
--     eval (var i)         γ = lookup i γ
--     eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
--     eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
--     eval (multibox ts u) γ = λ ξ ζ → {!!}
--     eval (down t)        γ = (eval t γ) refl≤ reflR
--     eval (pair t u)      γ = eval t γ , eval u γ
--     eval (fst t)         γ = π₁ (eval t γ)
--     eval (snd t)         γ = π₂ (eval t γ)
--     eval tt              γ = ∙

--     eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
--     eval⋆ {⌀}     ∙        γ = ∙
--     eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- module EwaldEtAl where
--   open import BasicIS4.KripkeSemantics.EwaldEtAl public

--   --   w′  R  v′      w′  R  v′
--   --   ●╌╌╌╌╌╌◌       ◌╌╌╌╌╌╌●
--   --   │      ┊       ┊      │
--   -- ≤ │   ₁  ┊ ≤   ≤ ┊   ₂  │ ≤
--   --   │      ┊       ┊      │
--   --   ●──────●       ●──────●
--   --   w   R  v       w   R  v
--   --
--   -- slice     : ∀ {v w w′} → w R v → w ≤ w′ → ∃ (λ v′ → w′ R v′ × v ≤ v′)
--   -- switch≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

--   mutual
--     eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
--     eval (var i)         γ = lookup i γ
--     eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
--     eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
--     eval (multibox ts u) γ = λ ξ ζ → {!!}
--     eval (down t)        γ = (eval t γ) refl≤ reflR
--     eval (pair t u)      γ = eval t γ , eval u γ
--     eval (fst t)         γ = π₁ (eval t γ)
--     eval (snd t)         γ = π₂ (eval t γ)
--     eval tt              γ = ∙

--     eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
--     eval⋆ {⌀}     ∙        γ = ∙
--     eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- module AlechinaEtAl where
--   open import BasicIS4.KripkeSemantics.AlechinaEtAl public

--   --   w′  R  v′
--   --   ◌╌╌╌╌╌╌●
--   --   ┊      │
--   -- ≤ ┊   ₂  │ ≤
--   --   ┊      │
--   --   ●──────●
--   --   w   R  v
--   --
--   -- switch≤⨾R : ∀ {w v v′} → v ≤ v′ → w R v → ∃ (λ w′ → w ≤ w′ × w′ R v′)

--   mutual
--     eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
--     eval (var i)         γ = lookup i γ
--     eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
--     eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
--     eval (multibox ts u) γ = λ ξ ζ → {!!}
--     eval (down t)        γ = (eval t γ) refl≤ reflR
--     eval (pair t u)      γ = eval t γ , eval u γ
--     eval (fst t)         γ = π₁ (eval t γ)
--     eval (snd t)         γ = π₂ (eval t γ)
--     eval tt              γ = ∙

--     eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
--     eval⋆ {⌀}     ∙        γ = ∙
--     eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
