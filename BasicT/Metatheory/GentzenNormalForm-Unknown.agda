module BasicT.Metatheory.GentzenNormalForm-Unknown where

open import BasicT.Syntax.GentzenNormalForm public


-- Forcing.  (In a particular model?)

infix 3 _⊩_
_⊩_ : Cx Ty → Ty → Set
Γ ⊩ α P   = Γ ⊢ⁿᶠ α P
Γ ⊩ A ▻ B = Γ ⊢ⁿᵉ A ▻ B ⊎ ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⊩ A → Γ′ ⊩ B
Γ ⊩ A ∧ B = Γ ⊢ⁿᵉ A ∧ B ⊎ Γ ⊩ A × Γ ⊩ B
Γ ⊩ ⊤    = Γ ⊢ⁿᶠ ⊤
Γ ⊩ BOOL  = Γ ⊢ⁿᶠ BOOL
Γ ⊩ NAT   = Γ ⊢ⁿᶠ NAT

infix 3 _⊩⋆_
_⊩⋆_ : Cx Ty → Cx Ty → Set
Γ ⊩⋆ ∅     = 𝟙
Γ ⊩⋆ Ξ , A = Γ ⊩⋆ Ξ × Γ ⊩ A


-- Monotonicity with respect to context inclusion.

mono⊩ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ A → Γ′ ⊩ A
mono⊩ {α P}   η t      = mono⊢ⁿᶠ η t
mono⊩ {A ▻ B} η (ι₁ t) = ι₁ (mono⊢ⁿᵉ η t)
mono⊩ {A ▻ B} η (ι₂ s) = ι₂ (λ η′ a → s (trans⊆ η η′) a)
mono⊩ {A ∧ B} η (ι₁ t) = ι₁ (mono⊢ⁿᵉ η t)
mono⊩ {A ∧ B} η (ι₂ s) = ι₂ (mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s))
mono⊩ {⊤}    η t      = mono⊢ⁿᶠ η t
mono⊩ {BOOL}  η t      = mono⊢ⁿᶠ η t
mono⊩ {NAT}   η t      = mono⊢ⁿᶠ η t

mono⊩⋆ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Ξ → Γ′ ⊩⋆ Ξ
mono⊩⋆ {∅}     η ∙       = ∙
mono⊩⋆ {Ξ , A} η (γ , a) = mono⊩⋆ {Ξ} η γ , mono⊩ {A} η a


-- Soundness and completeness.  (With respect to a particular model?)

reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
reflect {α P}   t = neⁿᶠ t
reflect {A ▻ B} t = ι₁ t
reflect {A ∧ B} t = ι₁ t
reflect {⊤}    t = neⁿᶠ t
reflect {BOOL}  t = neⁿᶠ t
reflect {NAT}   t = neⁿᶠ t

reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
reify {α P}   t      = t
reify {A ▻ B} (ι₁ t) = neⁿᶠ t
reify {A ▻ B} (ι₂ s) = lamⁿᶠ (reify (s weak⊆ (reflect {A} (varⁿᵉ top))))
reify {A ∧ B} (ι₁ t) = neⁿᶠ t
reify {A ∧ B} (ι₂ s) = pairⁿᶠ (reify (π₁ s)) (reify (π₂ s))
reify {⊤}    t      = t
reify {BOOL}  t      = t
reify {NAT}   t      = t

reflect⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ⁿᵉ Ξ → Γ ⊩⋆ Ξ
reflect⋆ {∅}     ∙        = ∙
reflect⋆ {Ξ , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Ξ Γ} → Γ ⊩⋆ Ξ → Γ ⊢⋆ⁿᶠ Ξ
reify⋆ {∅}     ∙        = ∙
reify⋆ {Ξ , A} (ts , t) = reify⋆ ts , reify t


-- Additional useful equipment.

_⟪$⟫_ : ∀ {A B w} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
ι₁ t ⟪$⟫ a = reflect (appⁿᵉ t (reify a))
ι₂ s ⟪$⟫ a = s refl⊆ a

⟪π₁⟫ : ∀ {A B w} → w ⊩ A ∧ B → w ⊩ A
⟪π₁⟫ (ι₁ t) = reflect (fstⁿᵉ t)
⟪π₁⟫ (ι₂ s) = π₁ s

⟪π₂⟫ : ∀ {A B w} → w ⊩ A ∧ B → w ⊩ B
⟪π₂⟫ (ι₁ t) = reflect (sndⁿᵉ t)
⟪π₂⟫ (ι₂ s) = π₂ s

⟪if⟫ : ∀ {C w} → w ⊩ BOOL → w ⊩ C → w ⊩ C → w ⊩ C
⟪if⟫ {C} (neⁿᶠ t) s₂ s₃ = reflect {C} (ifⁿᵉ t (reify s₂) (reify s₃))
⟪if⟫ {C} trueⁿᶠ   s₂ s₃ = s₂
⟪if⟫ {C} falseⁿᶠ  s₂ s₃ = s₃

⟪it⟫ : ∀ {C w} → w ⊩ NAT → w ⊩ C ▻ C → w ⊩ C → w ⊩ C
⟪it⟫ {C} (neⁿᶠ t)  s₂ s₃ = reflect {C} (itⁿᵉ t (reify s₂) (reify s₃))
⟪it⟫ {C} zeroⁿᶠ    s₂ s₃ = s₃
⟪it⟫ {C} (sucⁿᶠ t) s₂ s₃ = s₂ ⟪$⟫ ⟪it⟫ t s₂ s₃

⟪rec⟫ : ∀ {C w} → w ⊩ NAT → w ⊩ NAT ▻ C ▻ C → w ⊩ C → w ⊩ C
⟪rec⟫ {C} (neⁿᶠ t)  s₂ s₃ = reflect {C} (recⁿᵉ t (reify s₂) (reify s₃))
⟪rec⟫ {C} zeroⁿᶠ    s₂ s₃ = s₃
⟪rec⟫ {C} (sucⁿᶠ t) s₂ s₃ = (s₂ ⟪$⟫ t) ⟪$⟫ ⟪rec⟫ t s₂ s₃


-- Forcing for sequents.  (In a particular world of a particular model?)

infix 3 _⊩_⇒_
_⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

infix 3 _⊩_⇒⋆_
_⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
w ⊩ Γ ⇒⋆ Ξ = w ⊩⋆ Γ → w ⊩⋆ Ξ


-- Entailment.  (Forcing in all worlds of all models, for sequents?)

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set
Γ ⊨ A = ∀ {w : Cx Ty} → w ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set
Γ ⊨⋆ Ξ = ∀ {w : Cx Ty} → w ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
lookup top     (γ , a) = a
lookup (pop i) (γ , b) = lookup i γ


-- Evaluation.  (Soundness with respect to all models?)

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)         γ = lookup i γ
eval (lam t)         γ = ι₂ (λ η a → eval t (mono⊩⋆ η γ , a))
eval (app t u)       γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u)      γ = ι₂ (eval t γ , eval u γ)
eval (fst t)         γ = ⟪π₁⟫ (eval t γ)
eval (snd t)         γ = ⟪π₂⟫ (eval t γ)
eval unit            γ = unitⁿᶠ
eval true            γ = trueⁿᶠ
eval false           γ = trueⁿᶠ
eval (if {C} t u v)  γ = ⟪if⟫ {C} (eval t γ) (eval u γ) (eval v γ)
eval zero            γ = zeroⁿᶠ
eval (suc t)         γ = sucⁿᶠ (eval t γ)
eval (it {C} t u v)  γ = ⟪it⟫ {C} (eval t γ) (eval u γ) (eval v γ)
eval (rec {C} t u v) γ = ⟪rec⟫ {C} (eval t γ) (eval u γ) (eval v γ)

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ = ∙
eval⋆ {Ξ , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆ⁿᵉ

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = eval⋆ (trans⊢⋆ (nf→tm⋆ (reify⋆ ts)) (nf→tm⋆ (reify⋆ us))) refl⊩⋆


-- Quotation.  (Completeness with respect to all models?)

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = nf→tm (reify (s refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
