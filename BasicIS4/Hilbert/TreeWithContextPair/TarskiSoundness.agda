module BasicIS4.Hilbert.TreeWithContextPair.TarskiSoundness where

open import BasicIS4.Hilbert.TreeWithContextPair public
open import BasicIS4.TarskiSemantics public


module Closed where
  open TruthWithClosedBox (ClosedBox) public

  -- FIXME: This formalisation seems to prohibit closed syntax.
  postulate
    oops : ∀ {A Δ} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ⌀ ⊢ A

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)   γ δ = lookup i γ
  eval (app t u) γ δ = (eval t γ δ) (eval u γ δ)
  eval ci        γ δ = id
  eval ck        γ δ = const
  eval cs        γ δ = ap
  eval (mvar i)  γ δ = lookup i δ
  eval (box t)   γ δ = [ oops t ] , eval t ∙ δ
  eval cdist     γ δ = λ { ([ t ] , f) ([ u ] , a) → [ app t u ] , f a }
  eval cup       γ δ = λ { ([ t ] , a) → [ box t ] , ([ t ] , a) }
  eval cdown     γ δ = λ { ([ t ] , a) → a }
  eval cpair     γ δ = _,_
  eval cfst      γ δ = π₁
  eval csnd      γ δ = π₂
  eval tt        γ δ = ∙


module Strange where
  open TruthWithClosedBox (StrangeBox) public

  -- FIXME: Modal contexts of strange syntax are not connected to each other.
  postulate
    oops : ∀ {A Δ Δ′} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ Δ′ ⊢ A

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)   γ δ = lookup i γ
  eval (app t u) γ δ = (eval t γ δ) (eval u γ δ)
  eval ci        γ δ = id
  eval ck        γ δ = const
  eval cs        γ δ = ap
  eval (mvar i)  γ δ = lookup i δ
  eval (box t)   γ δ = [ t ] , eval t ∙ δ
  eval cdist     γ δ = λ { ([ t ] , f) ([ u ] , a) → [ app t (oops u) ] , f a }
  eval cup       γ δ = λ { ([ t ] , a) → [ box t ] , ([ t ] , a) }
  eval cdown     γ δ = λ { ([ t ] , a) → a }
  eval cpair     γ δ = _,_
  eval cfst      γ δ = π₁
  eval csnd      γ δ = π₂
  eval tt        γ δ = ∙


module Open where
  open TruthWithOpenBox (OpenBox) public

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var {A} i)      γ δ = mono⊨ {A} bot⊆ (lookup i γ)
  eval (app t u)        γ δ = (eval t γ δ) refl⊆ (eval u γ δ)
  eval ci               γ δ = λ _ → id
  eval (ck {A})         γ δ = λ _ a θ b → mono⊨ {A} θ a
  eval (cs {A} {B} {C}) γ δ = λ _ f θ g θ′ a →
                              let h = ((mono⊨ {A ▻ B ▻ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                                  b = (mono⊨ {A ▻ B} θ′ g) refl⊆ a
                              in  h b
  eval (mvar {A} i)     γ δ = mono⊨ {A} bot⊆ (lookup i δ)
  eval (box {A} t)      γ δ = λ θ → [ mmono⊢ θ t ]
                                     , mono⊨ {A} θ (eval t ∙ δ)
  eval cdist            γ δ = λ _ □f θ □a θ′ →
                              let [ t ] , f = □f (trans⊆ θ θ′)
                                  [ u ] , a = □a θ′
                              in  [ app t u ] , f refl⊆ a
  eval (cup {A})        γ δ = λ _ □a θ →
                              let [ t ] , a = □a refl⊆
                              in  [ mmono⊢ θ (box t) ]
                                  , (λ θ′ → [ mmono⊢ (trans⊆ θ θ′) t ]
                                             , mono⊨ {A} (trans⊆ θ θ′) a)
  eval cdown            γ δ = λ _ □a →
                              let [ t ] , a = □a refl⊆
                              in  a
  eval (cpair {A})      γ δ = λ _ a θ b → mono⊨ {A} θ a , b
  eval cfst             γ δ = λ _ → π₁
  eval csnd             γ δ = λ _ → π₂
  eval tt               γ δ = ∙
