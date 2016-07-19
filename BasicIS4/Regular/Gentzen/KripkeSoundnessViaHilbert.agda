module BasicIS4.Regular.Gentzen.KripkeSoundnessViaHilbert where

open import BasicIS4.Regular.Gentzen public

import BasicIS4.Regular.Hilbert.KripkeSoundness as KS
import BasicIS4.Regular.Translation as T


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
