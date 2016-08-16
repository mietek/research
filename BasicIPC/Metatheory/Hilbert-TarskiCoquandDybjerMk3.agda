module BasicIPC.Metatheory.Hilbert-TarskiCoquandDybjerMk3 where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiCoquandDybjerMk3 public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A Γ} → Γ ⊨ A → [ Γ ⊢ A ]
reify {α P}   (t , s) = t
reify {A ▻ B} s       = let t , f = s refl⊆ in t
reify {A ∧ B} (a , b) = [app] ([app] [cpair] (reify {A} a)) (reify {B} b)
reify {⊤}    ∙       = [tt]

reify⋆ : ∀ {{_ : Model}} {Π Γ} → Γ ⊨⋆ Π → [ Γ ⊢⋆ Π ]
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)     γ = lookup i γ
eval (app t u)   γ = eval t γ ⟪$⟫ eval u γ
eval ci          γ = λ _ → [ci] , id
eval (ck {A})    γ = λ _ → [ck] , λ a η →
                     let a′ = mono⊨ {A} η a
                     in  [app] [ck] (reify a′) , const a′
eval cs          γ = λ _ → [cs] , λ s η →
                     let t , f = s η
                     in  [app] [cs] t , λ s′ η′ →
                         let t′ , f′ = s (trans⊆ η η′)
                             u  , g = s′ η′
                         in  [app] ([app] [cs] t′) u , λ a →
                             let _ , h = (f′ a) refl⊆
                             in  h (g a)
eval (cpair {A}) γ = λ _ → [cpair] , λ a η →
                     let a′ = mono⊨ {A} η a
                     in  [app] [cpair] (reify a′) , _,_ a′
eval cfst        γ = λ _ → [cfst] , π₁
eval csnd        γ = λ _ → [csnd] , π₂
eval tt          γ = ∙

eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → ∀ᴹ⊨ Γ ⇒⋆ Π
eval⋆ {⌀}     ∙        γ = ∙
eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- -- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊨ᵅ_    = λ Γ P → Γ ⊢ α P
    ; mono⊨ᵅ  = mono⊢
    ; [_⊢_]   = _⊢_
    ; [mono⊢] = mono⊢
    ; [app]    = app
    ; [ci]     = ci
    ; [ck]     = ck
    ; [cs]     = cs
    ; [cpair]  = cpair
    ; [cfst]   = cfst
    ; [csnd]   = csnd
    ; [tt]     = tt
    }


-- Soundness with respect to the canonical model.

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η → mono⊢ η t , λ a → reflect {B} (app (mono⊢ η t) (reify {A} a))
reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity.

refl⊨⋆ : ∀ {Γ} → Γ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆

-- TODO: Transitivity.


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → ∀ᴹ⊨ Γ ⇒ A → Γ ⊢ A
quot t = reify (t refl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
