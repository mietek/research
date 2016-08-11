module BasicIS4.Hilbert.TreeWithContextPair.KripkeSoundness where

open import BasicIS4.Hilbert.TreeWithContextPair public


-- Soundness, or evaluation, with only modal accessibility.

module WithRegularForcing where
  open import BasicIS4.KripkeSemantics public
  open RegularForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ reflR)
  eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ζ →
                              let ζ′ = ≤⨾R→R (_ , (ξ , ζ))
                                  f  = □f ζ′ refl≤
                                  a  = □a ζ
                              in  f a
  eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ δ = λ _ □a → □a reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


-- Soundness, or evaluation, with both intuitionistic and modal accessibility.

module WithBidirectionalForcing where
  open import BasicIS4.KripkeSemantics public
  open DualRelationForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box t)          γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                              in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
                              let f = □f (trans≤ ξ ξ′) ζ refl≤
                                  a = □a ξ′ ζ
                              in  f a
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                              in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙


-- The remaining soundness proofs are subsumed by the above.

module Ono where
  open import BasicIS4.KripkeSemantics.Ono public
  open RegularForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ reflR)
  eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ζ →
                              let ζ′ = ≤⨾R→R (_ , (ξ , ζ))
                                  f  = □f ζ′ refl≤
                                  a  = □a ζ
                              in  f a
  eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ δ = λ _ □a → □a reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙

module BozicDosen where
  open import BasicIS4.KripkeSemantics.BozicDosen public
  open RegularForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ reflR)
  eval (box t)          γ δ = λ ζ → eval t ∙ (λ ζ′ → δ (transR ζ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ζ →
                              let _ , (ξ′ , ζ′) = ≤⨾R→R⨾≤ (_ , (ξ , ζ))
                                  f = □f ξ′ ζ′
                                  a = □a ζ
                              in  f a
  eval cup              γ δ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ δ = λ _ □a → □a reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙

module EwaldEtAl where
  open import BasicIS4.KripkeSemantics.EwaldEtAl public
  open DualRelationForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box {A} t)      γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                              in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
                              let f = □f (trans≤ ξ ξ′) ζ refl≤
                                  a = □a ξ′ ζ
                              in  f a
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                              in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙

module AlechinaEtAl where
  open import BasicIS4.KripkeSemantics.AlechinaEtAl public
  open DualRelationForcing public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊩ A
  eval (var i)          γ δ = lookup i γ
  eval (app t u)        γ δ = (eval t γ δ refl≤) (eval u γ δ)
  eval ci               γ δ = λ _ a → a
  eval (ck {A})         γ δ = λ _ a ξ b → mono⊩ {A} ξ a
  eval (cs {A} {B} {C}) γ δ = λ _ f ξ g ξ′ a →
                              let h = ((mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) f) refl≤ a) refl≤
                                  b = (mono⊩ {A ▻ B} ξ′ g) refl≤ a
                              in  h b
  eval (mvar i)         γ δ = lookup i (δ refl≤ reflR)
  eval (box t)          γ δ = λ ξ ζ → eval t ∙ (λ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = R⨾≤→≤⨾R (_ , (ζ , ξ′))
                              in  δ (trans≤ ξ ξ″) (transR ζ″ ζ′))
  eval cdist            γ δ = λ _ □f ξ □a ξ′ ζ →
                              let f = □f (trans≤ ξ ξ′) ζ refl≤
                                  a = □a ξ′ ζ
                              in  f a
  eval cup              γ δ = λ _ □a ξ ζ ξ′ ζ′ →
                              let _ , (ξ″ , ζ″) = trans≤⨾R (_ , (ξ , ζ)) (_ , (ξ′ , ζ′))
                              in  □a ξ″ ζ″
  eval cdown            γ δ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ δ = λ _ a ξ b → mono⊩ {A} ξ a , b
  eval cfst             γ δ = λ _ s → π₁ s
  eval csnd             γ δ = λ _ s → π₂ s
  eval tt               γ δ = ∙
