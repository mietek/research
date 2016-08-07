module BasicIS4.Regular.Gentzen.TarskiSoundness where

open import BasicIS4.Regular.Gentzen public
open import BasicIS4.TarskiSemantics public

import BasicIS4.Regular.Hilbert.Nested.TarskiSoundness as HN
import BasicIS4.Regular.Translation as T


module Closed where
  open TruthWithClosedBox (ClosedBox) public
  open T
  open T.Closed

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval {A} t γ = hn⇒g {A} (HN.Closed.eval (g→hn t) (g⇒hn⋆ γ))

  -- FIXME: How to write this without translation?
  postulate
    oops : ∀ {A Δ} → □⋆ Δ ⊢ A → ⌀ ⊢ A

  mutual
    eval′ : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval′ (var i)         γ = lookup i γ
    eval′ (lam t)         γ = λ a → eval′ t (γ , a)
    eval′ (app t u)       γ = (eval′ t γ) (eval′ u γ)
    eval′ (multibox ts u) γ = [ oops u ] , eval′ u (eval′⋆ ts γ)
    eval′ (down t)        γ = let [ s ] , a = eval′ t γ
                             in  a
    eval′ (pair t u)      γ = eval′ t γ , eval′ u γ
    eval′ (fst t)         γ = π₁ (eval′ t γ)
    eval′ (snd t)         γ = π₂ (eval′ t γ)
    eval′ tt              γ = ∙

    eval′⋆ : ∀ {Δ Γ} → Γ ⊢⋆ Δ → Γ ᴹ⊨⋆ Δ
    eval′⋆ {⌀}     ∙        γ = ∙
    eval′⋆ {Δ , A} (ts , t) γ = eval′⋆ ts γ , eval′ t γ


module Strange where
  open TruthWithClosedBox (StrangeBox) public

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ a → eval t (γ , a)
    eval (app t u)       γ = (eval t γ) (eval u γ)
    eval (multibox ts u) γ = [ u ] , eval u (eval⋆ ts γ)
    eval (down t)        γ = let [ s ] , a = eval t γ
                             in  a
    eval (pair t u)      γ = eval t γ , eval u γ
    eval (fst t)         γ = π₁ (eval t γ)
    eval (snd t)         γ = π₂ (eval t γ)
    eval tt              γ = ∙

    eval⋆ : ∀ {Δ Γ} → Γ ⊢⋆ Δ → Γ ᴹ⊨⋆ Δ
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Δ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


module Open where
  open TruthWithOpenBox (OpenBox) public
  open T
  open T.Open

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval {A} t γ = hn⇒g {A} (HN.Open.eval (g→hn t) (g⇒hn⋆ γ))


  -- FIXME: How to write this without translation?
  postulate
    oops₁ : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⊨ A
    oops₂ : ∀ {A Δ Δ′} → □⋆ Δ ⊢ A → □⋆ Δ′ ⊢ A

  mutual
    eval′ : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval′ (var i)             γ = lookup i γ
    eval′ (lam {A} {B} t)     γ = λ _ a → mono⊨ {B} bot⊆ (eval′ t (γ , oops₁ {A} a))
    eval′ (app t u)           γ = (eval′ t γ) bot⊆ (eval′ u γ)
    eval′ (multibox {A} ts u) γ = λ _ → [ oops₂ u ]
                                         , mono⊨ {A} bot⊆ (eval′ u (eval′⋆ ts γ))
    eval′ (down t)            γ = let [ s ] , a = eval′ t γ refl⊆
                                  in  a
    eval′ (pair t u)          γ = eval′ t γ , eval′ u γ
    eval′ (fst t)             γ = π₁ (eval′ t γ)
    eval′ (snd t)             γ = π₂ (eval′ t γ)
    eval′ tt                  γ = ∙

    eval′⋆ : ∀ {Δ Γ} → Γ ⊢⋆ Δ → Γ ᴹ⊨⋆ Δ
    eval′⋆ {⌀}     ∙        γ = ∙
    eval′⋆ {Δ , A} (ts , t) γ = eval′⋆ ts γ , eval′ t γ
