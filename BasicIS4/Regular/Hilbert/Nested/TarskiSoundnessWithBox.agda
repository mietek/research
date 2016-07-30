module BasicIS4.Regular.Hilbert.Nested.TarskiSoundnessWithBox where

open import BasicIS4.Regular.Hilbert.Nested public
open import BasicIS4.TarskiSemantics public


module Closed where
  open TruthWithClosedBox (ClosedBox) public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval (box t)   γ = [ box t ] , eval t ∙
  eval cdist     γ = λ { ([ t ] , f) ([ u ] , a) → [ dist t u ] , f a }
  eval cup       γ = λ { ([ t ] , a) → [ up t ] , ([ t ] , a) }
  eval cdown     γ = λ { ([ t ] , a) → a }
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙


module Strange where
  open TruthWithClosedBox (StrangeBox) public

  -- FIXME: Modal contexts of strange syntax are not connected to each other.
  postulate
    oops : ∀ {A Δ Δ′} → □⋆ Δ ⊢ A → □⋆ Δ′ ⊢ A

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval (box t)   γ = [ lift t ] , eval t ∙
  eval cdist     γ = λ { ([ t ] , □f) ([ u ] , □a) → [ dist t (oops u) ] , □f □a }
  eval cup       γ = λ { ([ t ] , □a) → [ up t ] , ([ t ] , □a) }
  eval cdown     γ = λ { ([ t ] , □a) → □a }
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙


module Open where
  open TruthWithOpenBox (OpenBox) public

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl⊆ (eval u γ)
  eval ci               γ = λ _ → id
  eval (ck {A})         γ = λ _ a θ b → mono⊨ {A} θ a
  eval (cs {A} {B} {C}) γ = λ _ f θ g θ′ a →
                            let h = ((mono⊨ {A ▷ B ▷ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                                b = (mono⊨ {A ▷ B} θ′ g) refl⊆ a
                            in  h b
  eval (box {A} t)      γ = λ _ → [ mono⊢ bot⊆ (lift t) ]
                                   , mono⊨ {A} bot⊆ (eval t ∙)
  eval cdist            γ = λ _ □f θ □a θ′ →
                            let [ t ] , f = □f (trans⊆ θ θ′)
                                [ u ] , a = □a θ′
                            in  [ dist t u ] , f refl⊆ a
  eval (cup {A})        γ = λ _ □a θ →
                            let [ t ] , a = □a θ
                            in  [ up t ]
                                , (λ θ′ → [ mono⊢ (lift⊆ θ′) t ]
                                           , mono⊨ {A} θ′ a)
  eval cdown            γ = λ _ □a →
                            let [ t ] , a = □a refl⊆
                            in  a
  eval (cpair {A})      γ = λ _ a θ b → mono⊨ {A} θ a , b
  eval cfst             γ = λ _ → π₁
  eval csnd             γ = λ _ → π₂
  eval tt               γ = ∙
