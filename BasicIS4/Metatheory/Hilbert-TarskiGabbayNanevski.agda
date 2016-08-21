module BasicIS4.Metatheory.Hilbert-TarskiGabbayNanevski where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiGabbayNanevski public

open SyntacticComponent (_⊢_) (mono⊢) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ in t
  reify {□ A}   s       = let t , a = s refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪const⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪const⟫ {A} a η = let a′ = mono⊩ {A} η a
                    in  app ck (reify a′) , const a′

  ⟪ap⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ {A} {B} {C} s₁ η = let s₁′   = mono⊩ {A ▻ B ▻ C} η s₁
                               t , _ = s₁′ refl⊆
                           in  app cs t , λ s₂ η′ →
                                 let s₁″    = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                     t′ , _ = s₁″ refl⊆
                                     s₂′    = mono⊩ {A ▻ B} η′ s₂
                                     u  , g = s₂′ refl⊆
                                 in  app (app cs t′) u , ⟪ap⟫ s₁″ s₂′

  _⟪◎⟫_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A → Γ ⊩ □ B
  (s₁ ⟪◎⟫ s₂) η = let t , f = s₁ η
                      u , a = s₂ η
                  in  app (app cdist t) u , f ⟪$⟫ a

  -- TODO: Report bug.
  _⟪◎⟫′_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ  ⊩ □ A ▻ □ B
  _⟪◎⟫′_ {A} {B} s η = let s′ = mono⊩ {□ (A ▻ B)} η s
                       in  app cdist (reify (λ {Γ′} η′ → s′ η′ )) , _⟪◎⟫_ s′

  ⟪⇑⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ □ □ A
  ⟪⇑⟫ s η = let t , a = s η
            in  app cup t , λ η′ → s (trans⊆ η η′)

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η = let a′ = mono⊩ {A} η a
                   in  app cpair (reify a′) , _,_ a′


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = const (ci , id)
eval ck        γ = const (ck , ⟪const⟫)
eval cs        γ = const (cs , ⟪ap⟫′)
eval (box t)   γ = const (box t , eval t ∙)
eval cdist     γ = const (cdist , _⟪◎⟫′_)
eval cup       γ = const (cup , ⟪⇑⟫)
eval cdown     γ = const (cdown , ⟪⇓⟫)
eval cpair     γ = const (cpair , _⟪,⟫′_)
eval cfst      γ = const (cfst , π₁)
eval csnd      γ = const (csnd , π₂)
eval tt        γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { _⊩ᵅ_   = λ Γ P → Γ ⊢ α P
      ; mono⊩ᵅ = mono⊢
      }


-- Soundness with respect to the canonical model.

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η →
                      let t′ = mono⊢ η t
                      in  t′ , λ a → reflect (app t′ (reify a))
reflect {□ A}   t = λ η →
                      let t′ = mono⊢ η t
                      in  t′ , reflect (down t′)
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reify (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
