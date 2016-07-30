module BasicIS4.DualContext.Gentzen.TarskiSoundnessWithBox where

open import BasicIS4.DualContext.Gentzen public
open import BasicIS4.TarskiSemantics public

import BasicIS4.DualContext.Hilbert.Nested.TarskiSoundnessWithBox as HN
import BasicIS4.DualContext.Translation as T


module Closed where
  open TruthWithClosedBox (ClosedBox) public
  open T
  open T.Closed

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval {A} t γ δ = hn⇒g {A} (HN.Closed.eval (g→hn t) (g⇒hn⋆ γ) (g⇒hn⋆ δ))


module Strange where
  open TruthWithClosedBox (StrangeBox) public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ a → eval t (γ , a) δ
  eval (app t u)   γ δ = (eval t γ δ) (eval u γ δ)
  eval (mvar i)    γ δ = lookup i δ
  eval (box t)     γ δ = [ box t ] , eval t ∙ δ
  eval (unbox t u) γ δ = eval u γ (δ , π₂ (eval t γ δ))
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙


module Open where
  open TruthWithOpenBox (OpenBox) public
  open T
  open T.Open

  -- FIXME: How to write this without translation?
  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval {A} t γ δ = hn⇒g {A} (HN.Open.eval (g→hn t) (g⇒hn⋆ γ) (g⇒hn⋆ δ))
