module BasicIS4.Regular.Hilbert.Nested.KripkeSoundness where

open import BasicIS4.Regular.Hilbert.Nested public


-- Soundness, or evaluation, with only modal accessibility.

module WithRegularForcing where
  open import BasicIS4.KripkeSemantics public
  open RegularForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ζ →
                            let ζ′ = ≤⨾R→R (_ , (ξ , ζ))
                                f  = □f ζ′ refl≤
                                a  = □a ζ
                            in  f a
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


-- Soundness, or evaluation, with both intuitionistic and modal accessibility.

module WithDualRelationForcing where
  open import BasicIS4.KripkeSemantics public
  open DualRelationForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙


-- The remaining proofs are subsumed by the above.

module Ono where
  open import BasicIS4.KripkeSemantics.Ono public
  open RegularForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ζ →
                            let ζ′ = ≤⨾R→R (_ , (ξ , ζ))
                                f  = □f ζ′ refl≤
                                a  = □a ζ
                            in  f a
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙

module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public
  open RegularForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ζ →
                            let _ , (ζ′ , ξ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                                f = □f ζ′ ξ′
                                a = □a ζ
                            in  f a
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙

module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public
  open DualRelationForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙

module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public
  open DualRelationForcing public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ g ξ′ a →
                            let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                b = (mono⊩ {A ▷ B} ξ′ g) refl≤ a
                            in  h b
  eval (box t)          γ = λ ξ ζ → eval t ∙
  eval cdist            γ = λ _ □f ξ □a ξ′ ζ →
                            let f = □f (trans≤ ξ ξ′) ζ refl≤
                                a = □a ξ′ ζ
                            in  f a
  eval cup              γ = λ _ □a ξ ζ ξ′ ζ′ →
                            let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                            in  □a ξ″ ζ″
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ = λ _ s → π₁ s
  eval csnd             γ = λ _ s → π₂ s
  eval tt               γ = ∙
