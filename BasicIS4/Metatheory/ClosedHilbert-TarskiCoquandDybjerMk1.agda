module BasicIS4.Metatheory.ClosedHilbert-TarskiCoquandDybjerMk1 where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Syntax.TranslatedClosedHilbertEquipment public
open import BasicIS4.Semantics.TarskiCoquandDybjerMk1 public

open SyntacticComponent (λ Δ A → ⊢ □⋆ Δ ▻⋯▻ A)
                        (λ {Δ} {Δ′} → ᵀmono⊢ {□⋆ Δ} {□⋆ Δ′} ∘ lift⊆) public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⊢ □⋆ Δ ▻⋯▻ A
reify {α P}   {Δ} (t , s) = t
reify {A ▻ B} {Δ} s       = let t , f = s refl⊆
                            in  t
reify {□ A}   {Δ} □a      = let t , a = □a refl⊆
                            in  ᵀcxdown {Δ} (ᵀlift {□⋆ Δ} t)
reify {A ∧ B} {Δ} (a , b) = ᵀpair {□⋆ Δ} (reify {A} a) (reify {B} b)
reify {⊤}    {Δ} ∙       = ᵀmono⊢ {⌀} {□⋆ Δ} bot⊆ tt


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u)        = let _ , f = (eval t) refl⊆
                        in  f (eval u)
eval ci               = λ θ₀ → ᵀml θ₀ ci , id
eval (ck {A})         = λ θ₀ → ᵀml θ₀ ck , (λ a {Δ″} θ →
                          ᵀk₁ {□⋆ Δ″} (ᵀml θ (reify {A} a)) , (λ b →
                            mono⊨ {A} θ a))
eval (cs {A} {B} {C}) = λ θ₀ → ᵀml θ₀ cs , (λ f {Δ″} θ →
                        let t , f′ = f θ
                        in  ᵀs₁ {□⋆ Δ″} (ᵀml θ (reify {A ▻ B ▻ C} f)) , (λ g {Δ‴} θ′ →
                            let _ , f″ = f (trans⊆ θ θ′)
                                u , g′ = g θ′
                            in  ᵀs₂ {□⋆ Δ‴} (ᵀml (trans⊆ θ θ′) (reify {A ▻ B ▻ C} f))
                                            (ᵀml θ′ (reify {A ▻ B} g)) , (λ a →
                                let _ , h = (f″ a) refl⊆
                                    b     = g′ a
                                in  h b)))
eval (box {A} t)      = λ θ₀ → ᵀml θ₀ t , mono⊨ {A} bot⊆ (eval t)
eval (cdist {A} {B})  = λ θ₀ → ᵀml θ₀ cdist , (λ □f {Δ″} θ →
                        let t , f = □f θ
                        in  ᵀdist₁ {□⋆ Δ″} (ᵀml θ (reify {□ (A ▻ B)} □f)) , (λ □a {Δ‴} θ′ →
                            let u  , a  = □a θ′
                                t′ , f′ = f θ′
                            in  ᵀapp {□⋆ Δ‴} (ᵀml θ′ t) u , f′ a))
eval (cup {A})        = λ θ₀ → ᵀml θ₀ cup , (λ □a {Δ″} θ →
                        let t , a = □a θ
                        in  ᵀcxdown {Δ″} (ᵀlift {□⋆ Δ″} t) , (λ θ′ →
                              ᵀml θ′ t , mono⊨ {A} θ′ a))
eval cdown            = λ θ₀ → ᵀml θ₀ cdown , (λ □a →
                        let t , a = □a refl⊆
                        in  a)
eval (cpair {A})      = λ θ₀ → ᵀml θ₀ cpair , (λ a {Δ″} θ →
                                  ᵀpair₁ {□⋆ Δ″} (ᵀml θ (reify {A} a)) , (λ b →
                                    mono⊨ {A} θ a , b))
eval cfst             = λ θ₀ → ᵀml θ₀ cfst , π₁
eval csnd             = λ θ₀ → ᵀml θ₀ csnd , π₂
eval tt               = ∙


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

quot : ∀ {A} → ᴹ⊨ A → ⊢ A
quot {A} t = reify {A} t


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval
