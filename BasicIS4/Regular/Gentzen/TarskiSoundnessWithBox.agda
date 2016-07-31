module BasicIS4.Regular.Gentzen.TarskiSoundnessWithBox where

open import BasicIS4.Regular.Gentzen public
open import BasicIS4.TarskiSemantics public

import BasicIS4.Regular.Hilbert.Nested.TarskiSoundnessWithBox as HN
import BasicIS4.Regular.Translation as T


module Closed where
  open TruthWithClosedBox (ClosedBox) public
  open T
  open T.Closed

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval {A} t γ = hn⇒g {A} (HN.Closed.eval (g→hn t) (g⇒hn⋆ γ))


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

  -- FIXME: How to write this without translation?
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval {A} t γ = hn⇒g {A} (HN.Open.eval (g→hn t) (g⇒hn⋆ γ))
