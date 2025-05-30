{-# OPTIONS --sized-types #-}

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Kripke-style semantics with exploding abstract worlds, and glueing for □ only.

module A201607.WIP2.BasicIS4.Semantics.Sketch4 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


-- Intuitionistic Kripke-CPS models, with exploding worlds.

record Model : Set₁ where
  infix 3 _⊪ᵅ_ _[⊢]_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Modal accessibility; preorder.
    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- Strong forcing for atomic propositions; monotonic.
    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

    -- Exploding.
    _‼_ : World → Ty → Set

    -- TODO
    ⌊_⌋  : World → Cx² Ty Ty
    ⌈_⌉  : Cx² Ty Ty → World
    lem₁ : ∀ {w} → ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ≤ w
    lem₂ : ∀ {w} → (_⁏_ {Ty} ∅ (mod ⌊ ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⌋)) ≡ (∅ ⁏ mod ⌊ w ⌋)

    -- TODO
    ⌊_⌋ᴵ : ∀ {w w′} → w ≤ w′ → ⌊ w ⌋ ⊆² ⌊ w′ ⌋
    ⌈_⌉ᴵ : ∀ {Γ Δ Γ′ Δ′} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → ⌈ Γ ⁏ Δ ⌉ ≤ ⌈ Γ′ ⁏ Δ′ ⌉
    ⌊_⌋ᴿ : ∀ {w w′} → w R w′ → mod ⌊ w ⌋ ⊆ mod ⌊ w′ ⌋
    ⌈_⌉ᴿ : ∀ {Δ Δ′} → Δ ⊆ Δ′ → ⌈ ∅ ⁏ Δ ⌉ R ⌈ ∅ ⁏ Δ′ ⌉

    -- Gentzen-style syntax representation; monotonic.
    _[⊢]_    : Cx² Ty Ty → Ty → Set
    mono[⊢]  : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ [⊢] A → Γ′ ⁏ Δ [⊢] A
    mmono[⊢] : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ′ [⊢] A
    [var]     : ∀ {A Γ Δ}   → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [lam]     : ∀ {A B Γ Δ} → Γ , A ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ▻ B
    [app]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [mvar]    : ∀ {A Γ Δ}   → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]     : ∀ {A Γ Δ}   → ∅ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [unbox]   : ∀ {A C Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ , A [⊢] C → Γ ⁏ Δ [⊢] C
    [pair]    : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ∧ B
    [fst]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] A
    [snd]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] B
    [unit]    : ∀ {Γ Δ}     → Γ ⁏ Δ [⊢] ⊤


  -- Composition of accessibility.

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_


  -- Persistence condition.
  --
  --   w′      v′  →           v′
  --   ◌───R───●   →           ●
  --   │           →         ╱
  --   ≤  ξ,ζ      →       R
  --   │           →     ╱
  --   ●           →   ●
  --   w           →   w

  field
    ≤⨾R→R : ∀ {v′ w} → w ≤⨾R v′ → w R v′


  -- Minor persistence condition.
  --
  --   w′      v′  →           v′
  --   ◌───R───●   →           ●
  --   │           →           │
  --   ≤  ξ,ζ      →           ≤
  --   │           →           │
  --   ●           →   ●───R───◌
  --   w           →   w       v
  --
  --                   w″  →                   w″
  --                   ●   →                   ●
  --                   │   →                   │
  --             ξ′,ζ′ ≤   →                   │
  --                   │   →                   │
  --           ●───R───◌   →                   ≤
  --           │       v′  →                   │
  --      ξ,ζ  ≤           →                   │
  --           │           →                   │
  --   ●───R───◌           →   ●───────R───────◌
  --   w       v           →   w               v″

  ≤⨾R→R⨾≤ : ∀ {v′ w} → w ≤⨾R v′ → w R⨾≤ v′
  ≤⨾R→R⨾≤ {v′} ξ,ζ = v′ , (≤⨾R→R ξ,ζ , refl≤)

  reflR⨾≤ : ∀ {w} → w R⨾≤ w
  reflR⨾≤ {w} = w , (reflR , refl≤)

  transR⨾≤ : ∀ {w′ w w″} → w R⨾≤ w′ → w′ R⨾≤ w″ → w R⨾≤ w″
  transR⨾≤ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) = let v″ , (ζ″ , ξ″) = ≤⨾R→R⨾≤ (w′ , (ξ , ζ′))
                                                 in  v″ , (transR ζ ζ″ , trans≤ ξ″ ξ′)

  ≤→R : ∀ {v′ w} → w ≤ v′ → w R v′
  ≤→R {v′} ξ = ≤⨾R→R (v′ , (ξ , reflR))


  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx² Ty Ty → Cx Ty → Set
  Γ ⁏ Δ [⊢]⋆ ∅     = 𝟙
  Γ ⁏ Δ [⊢]⋆ Ξ , A = Γ ⁏ Δ [⊢]⋆ Ξ × Γ ⁏ Δ [⊢] A

  mmono[⊢]⋆ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ [⊢]⋆ Ξ → Γ ⁏ Δ′ [⊢]⋆ Ξ
  mmono[⊢]⋆ {∅}     θ ∙        = ∙
  mmono[⊢]⋆ {Ξ , A} θ (ts , t) = mmono[⊢]⋆ θ ts , mmono[⊢] θ t

  mrefl₀[⊢]⋆ : ∀ {Δ} → ∅ ⁏ Δ [⊢]⋆ Δ
  mrefl₀[⊢]⋆ {∅}     = ∙
  mrefl₀[⊢]⋆ {Δ , A} = mmono[⊢]⋆ weak⊆ mrefl₀[⊢]⋆ , [mvar] top

  [mlam] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A [⊢] B → Γ ⁏ Δ [⊢] □ A ▻ B
  [mlam] t = [lam] ([unbox] ([var] top) (mono[⊢] weak⊆ t))

  [mmulticut₀] : ∀ {Ξ A Γ Δ} → ∅ ⁏ Δ [⊢]⋆ Ξ → Γ ⁏ Ξ [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut₀] {∅}     ∙        u = mmono[⊢] bot⊆ u
  [mmulticut₀] {Ξ , B} (ts , t) u = [app] ([mmulticut₀] ts ([mlam] u)) ([box] t)

open Model {{…}} public


-- Strong forcing and forcing, in a particular world of a particular model.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′ : World} → w R w′ → Glue (∅ ⁏ mod ⌊ w′ ⌋ [⊢] A) (⌈ ∅ ⁏ mod ⌊ w′ ⌋ ⌉ ⊩ A)
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {C} {w′ : World} → w ≤ w′ → (∀ {w″ : World} → w′ ≤ w″ → w″ ⊪ A → w″ ‼ C) → w′ ‼ C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mutual
    mono⊪ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ s = mono⊪ᵅ ξ s
    mono⊪ {A ▻ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
    mono⊪ {□ A}   ξ s = λ ζ′ → s (transR (≤→R ξ) ζ′)
    mono⊪ {A ∧ B} ξ s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
    mono⊪ {⊤}    ξ s = ∙

    mono⊩ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

  mono⊩⋆ : ∀ {Ξ} {w w′ : World} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Ξ , A} ξ (γ , a) = mono⊩⋆ {Ξ} ξ γ , mono⊩ {A} ξ a


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} {w : World} → w ⊪ A ▻ B → w ⊩ A → w ⊩ B
  s ⟪$⟫ a = s refl≤ a

  return : ∀ {A} {w : World} → w ⊪ A → w ⊩ A
  return {A} a = λ ξ k → k refl≤ (mono⊪ {A} ξ a)

  bind : ∀ {A B} {w : World} → w ⊩ A → (∀ {w′ : World} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
  bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans≤ ξ ξ′) a′ refl≤ (λ ξ″ a″ → k′ (trans≤ ξ′ ξ″) a″))


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx² Ty Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ∅ ⁏ mod ⌊ w ⌋ [⊢]⋆ Δ → ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⊩⋆ Δ → w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ∅ ⁏ mod ⌊ w ⌋ [⊢]⋆ Δ → ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⊩⋆ Δ → w ⊩⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} {w : World} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


--


open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ [⊢] A
  [ var i ]     = [var] i
  [ lam t ]     = [lam] [ t ]
  [ app t u ]   = [app] [ t ] [ u ]
  [ mvar i ]    = [mvar] i
  [ box t ]     = [box] [ t ]
  [ unbox t u ] = [unbox] [ t ] [ u ]
  [ pair t u ]  = [pair] [ t ] [ u ]
  [ fst t ]     = [fst] [ t ]
  [ snd t ]     = [snd] [ t ]
  [ unit ]      = [unit]


-- Soundness with respect to all models, or evaluation.

module _ {{_ : Model}} where
  lem₃ : ∀ {w : World} {Ξ} → ∅ ⁏ mod ⌊ w ⌋ [⊢]⋆ Ξ → ∅ ⁏ mod ⌊ ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⌋ [⊢]⋆ Ξ
  lem₃ {w} ts rewrite lem₂ {w} = ts

  lem₄ : ∀ {w : World} {Ξ} → ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⊩⋆ Ξ → ⌈ ∅ ⁏ mod ⌊ ⌈ ∅ ⁏ mod ⌊ w ⌋ ⌉ ⌋ ⌉ ⊩⋆ Ξ
  lem₄ {w} ts rewrite lem₂ {w} = ts

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ ד δ = lookup i γ
eval (lam {A} {B} t)     γ ד δ = return {A ▻ B} λ ξ a →
                                   let (η , θ) = ⌊ ξ ⌋ᴵ
                                       ψ       = refl⊆ , θ
                                   in  eval t (mono⊩⋆ ξ γ , a)
                                              (mmono[⊢]⋆ θ ד)
                                              (mono⊩⋆ ⌈ ψ ⌉ᴵ δ)
eval (app {A} {B} t u)   γ ד δ = bind {A ▻ B} {B} (eval t γ ד δ) λ ξ f →
                                   let (η , θ) = ⌊ ξ ⌋ᴵ
                                       ψ      = refl⊆ , θ
                                   in _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ ξ γ)
                                                              (mmono[⊢]⋆ θ ד)
                                                              (mono⊩⋆ ⌈ ψ ⌉ᴵ δ))
eval (mvar {A} i)        γ ד δ = mono⊩ {A} lem₁ (lookup i δ)
eval (box {A} t)         γ ד δ = return {□ A} λ ζ →
                                   let θ       = ⌊ ζ ⌋ᴿ
                                       ψ       = refl⊆ , θ
                                   in  mono[⊢] bot⊆ ([mmulticut₀] (mmono[⊢]⋆ θ ד) [ t ]) ⅋
                                         eval t ∙
                                                (lem₃ (mmono[⊢]⋆ θ ד))
                                                (lem₄ (mono⊩⋆ ⌈ ψ ⌉ᴵ δ))
eval (unbox {A} {C} t u) γ ד δ = bind {□ A} {C} (eval t γ ד δ) λ ξ a →
                                   let (η , θ) = ⌊ ξ ⌋ᴵ
                                       ψ       = refl⊆ , θ
                                   in  eval u (mono⊩⋆ ξ γ)
                                              (mmono[⊢]⋆ θ ד , syn (a reflR))
                                              (mono⊩⋆ ⌈ ψ ⌉ᴵ δ , sem (a reflR))
eval (pair {A} {B} t u)  γ ד δ = return {A ∧ B} (eval t γ ד δ , eval u γ ד δ)
eval (fst {A} {B} t)     γ ד δ = bind {A ∧ B} {A} (eval t γ ד δ) (K π₁)
eval (snd {A} {B} t)     γ ד δ = bind {A ∧ B} {B} (eval t γ ד δ) (K π₂)
eval unit                γ ד δ = return {⊤} ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ ד δ = ∙
eval⋆ {Ξ , A} (ts , t) γ ד δ = eval⋆ ts γ ד δ , eval t γ ד δ


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { World     = Cx² Ty Ty
      ; _≤_       = _⊆²_
      ; refl≤     = refl⊆²
      ; trans≤    = trans⊆²
      ; _R_       = λ { (Γ ⁏ Δ) (Γ′ ⁏ Δ′) → Δ ⊆ Δ′ }
      ; reflR     = refl⊆
      ; transR    = trans⊆
      ; _⊪ᵅ_     = λ { (Γ ⁏ Δ) P → Γ ⁏ Δ ⊢ⁿᵉ α P }
      ; mono⊪ᵅ   = mono²⊢ⁿᵉ
      ; _‼_       = λ { (Γ ⁏ Δ) A → Γ ⁏ Δ ⊢ⁿᶠ A }
      ; ⌊_⌋       = I
      ; ⌈_⌉       = I
      ; lem₁      = bot⊆ , refl⊆
      ; lem₂      = refl
      ; ⌊_⌋ᴵ      = I
      ; ⌈_⌉ᴵ      = I
      ; ⌊_⌋ᴿ      = I
      ; ⌈_⌉ᴿ      = I
      ; _[⊢]_    = _⊢_
      ; mono[⊢]  = mono⊢
      ; mmono[⊢] = mmono⊢
      ; [var]     = var
      ; [lam]     = lam
      ; [app]     = app
      ; [mvar]    = mvar
      ; [box]     = box
      ; [unbox]   = unbox
      ; [pair]    = pair
      ; [fst]     = fst
      ; [snd]     = snd
      ; [unit]    = unit
      ; ≤⨾R→R    = λ { (w′ , ((η , θ) , θ′)) → trans⊆ θ θ′ }
      }


-- Soundness and completeness with respect to the canonical model.

module _ {U : Set} where
  grab∈ : ∀ {A : U} {Γ Γ′} → Γ , A ⊆ Γ′ → A ∈ Γ′
  grab∈ (skip η) = pop (grab∈ η)
  grab∈ (keep η) = top

mutual
  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}   k = k refl⊆² λ ξ s → neⁿᶠ s
  reifyᶜ {A ▻ B} k = k refl⊆² λ ξ s → lamⁿᶠ (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} (varⁿᵉ top))))
  reifyᶜ {□ A}   k = k refl⊆² λ {w} ξ s → boxⁿᶠ (syn (s {w} refl⊆))
  reifyᶜ {A ∧ B} k = k refl⊆² λ ξ s → pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
  reifyᶜ {⊤}    k = k refl⊆² λ ξ s → unitⁿᶠ

  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}   t = return {α P} t
  reflectᶜ {A ▻ B} t = return {A ▻ B} λ { (η , θ) a →
                         reflectᶜ {B} (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
  reflectᶜ {□ A}   t = λ { (η , θ) k →
                         neⁿᶠ (unboxⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (k (refl⊆ , weak⊆) λ θ′ →
                           mvar (grab∈ θ′) ⅋
                             reflectᶜ {A} (mvarⁿᵉ (grab∈ θ′))))}
  reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t))
  reflectᶜ {⊤}    t = return {⊤} ∙

reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
reifyᶜ⋆ {∅}     ∙        = ∙
reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
reflectᶜ⋆ {∅}     ∙        = ∙
reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- Reflexivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

mrefl₀⊢⋆ⁿᵉ : ∀ {Δ} → ∅ ⁏ Δ ⊢⋆ⁿᵉ Δ
mrefl₀⊢⋆ⁿᵉ {∅}     = ∙
mrefl₀⊢⋆ⁿᵉ {Γ , A} = mmono⊢⋆ⁿᵉ weak⊆ mrefl₀⊢⋆ⁿᵉ , mvarⁿᵉ top

mrefl₀⊩⋆ : ∀ {Δ} → ∅ ⁏ Δ ⊩⋆ Δ
mrefl₀⊩⋆ = reflectᶜ⋆ mrefl₀⊢⋆ⁿᵉ


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
quot s = reifyᶜ (s refl⊩⋆ mrefl₀[⊢]⋆ mrefl₀⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
norm = quot ∘ eval
