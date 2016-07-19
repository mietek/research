module BasicIS4.Regular.Gentzen.KripkeSoundness where

open import BasicIS4.Regular.Gentzen public


module Ono where
  open import BasicIS4.KripkeSemantics.Ono

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → {!!}
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ζ → {!!}
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module Wijesekera where
  open import BasicIS4.KripkeSemantics.Wijesekera

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → {!!}
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → {!!}
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (mono⊩⋆ ξ γ , a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval (multibox ts u) γ = λ ξ ζ → {!!}
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
