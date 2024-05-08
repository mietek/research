{-# OPTIONS --allow-unsolved-metas #-}

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Kripke-style semantics with exploding abstract worlds, and glueing for □ only.

module A201607.WIP2.BasicIS4.Semantics.Sketch5 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


-- Intuitionistic modal Kripke-CPS models, with exploding worlds.

record Model : Set₁ where
  infix 3 _⊪ᵅ_ _[⊢]_
  infix 5 _≤_ _R_
  infixl 5 _[,]_ _[m,]_

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

  -- Composition of intuitionistic and modal accessibility.
  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  -- Composition of modal and intuitionistic accessibility.
  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  field
    -- Persistence condition.
    --   w′      v′  →           v′
    --   ◌───R───●   →           ●
    --   │           →         ╱
    --   ≤  ξ,ζ      →       R
    --   │           →     ╱
    --   ●           →   ●
    --   w           →   w
    ≤⨾R→R : ∀ {v′ w} → w ≤⨾R v′ → w R v′

    -- TODO
    ⌊_⌋    : World → World
    ≤→⌊≤⌋ : ∀ {w w′} → w ≤ w′ → ⌊ w ⌋ ≤ ⌊ w′ ⌋
    R→⌊≤⌋ : ∀ {w w′} → w R w′ → ⌊ w ⌋ ≤ ⌊ w′ ⌋
    lem₁   : ∀ {w} → ⌊ w ⌋ ≤ w
    lem₂   : ∀ {w} → ⌊ w ⌋ ≤ ⌊ ⌊ w ⌋ ⌋
    lem₃   : ∀ {w} → ⌊ ⌊ w ⌋ ⌋ ≤ ⌊ w ⌋ -- Unneeded

    -- TODO
    [∅]    : World
    _[,]_  : World → Ty → World
    _[m,]_ : World → Ty → World
    _[∈]_  : Ty → World → Set
    _[m∈]_ : Ty → World → Set

    -- Gentzen-style syntax; monotonic.
    _[⊢]_   : World → Ty → Set
    mono[⊢] : ∀ {A w w′} → w ≤ w′ → w [⊢] A → w′ [⊢] A
    [var]    : ∀ {A w}   → A [∈] w → w [⊢] A
    [lam]    : ∀ {A B w} → w [,] A [⊢] B → w [⊢] A ▻ B
    [app]    : ∀ {A B w} → w [⊢] A ▻ B → w [⊢] A → w [⊢] B
    [mvar]   : ∀ {A w}   → A [m∈] w → w [⊢] A
    [box]    : ∀ {A w}   → ⌊ w ⌋ [⊢] A → w [⊢] □ A
    [unbox]  : ∀ {A C w} → w [⊢] □ A → w [m,] A [⊢] C → w [⊢] C
    [pair]   : ∀ {A B w} → w [⊢] A → w [⊢] B → w [⊢] A ∧ B
    [fst]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] A
    [snd]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] B
    [unit]   : ∀ {w}     → w [⊢] ⊤

    -- Syntax in normal form.
    _[⊢ⁿᶠ]_ : World → Ty → Set

    -- Strong forcing for atomic propositions; monotonic.
    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

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
  _[⊢]⋆_ : World → Cx Ty → Set
  w [⊢]⋆ ∅     = 𝟙
  w [⊢]⋆ Ξ , A = w [⊢]⋆ Ξ × w [⊢] A

  mono[⊢]⋆ : ∀ {Ξ w w′} → w ≤ w′ → w [⊢]⋆ Ξ → w′ [⊢]⋆ Ξ
  mono[⊢]⋆ {∅}     ξ ∙        = ∙
  mono[⊢]⋆ {Ξ , A} ξ (ts , t) = mono[⊢]⋆ ξ ts , mono[⊢] ξ t

open Model {{…}} public


-- Strong forcing and forcing, in a particular world of a particular model.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′ : World} → w R w′ → Glue (⌊ w′ ⌋ [⊢] A) (⌊ w′ ⌋ ⊩ A)
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {C} {w′ : World} → w ≤ w′ → (∀ {w″ : World} → w′ ≤ w″ → w″ ⊪ A → w″ [⊢ⁿᶠ] C) → w′ [⊢ⁿᶠ] C

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
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} {w : World} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


--


open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  ⌈_⌉ : Cx² Ty Ty → World
  ⌈ ∅     ⁏ ∅     ⌉ = [∅]
  ⌈ Γ , A ⁏ ∅     ⌉ = ⌈ Γ ⁏ ∅ ⌉ [,] A
  ⌈ ∅     ⁏ Δ , B ⌉ = ⌈ ∅ ⁏ Δ ⌉ [m,] B
  ⌈ Γ , A ⁏ Δ , B ⌉ = ⌈ Γ ⁏ Δ ⌉ [,] A [m,] B

  postulate
    lemᵢ  : ∀ {Δ Γ A} → A [∈] ⌈ Γ , A ⁏ Δ ⌉
    lemᵢᵢ : ∀ {Δ Γ A B} → A [∈] ⌈ Γ ⁏ Δ ⌉ → A [∈] ⌈ Γ , B ⁏ Δ ⌉
    lemₘ : ∀ {Γ Δ A} → A [m∈] ⌈ Γ ⁏ Δ , A ⌉
    lemₘₘ : ∀ {Γ Δ A B} → A [m∈] ⌈ Γ ⁏ Δ ⌉ → A [m∈] ⌈ Γ ⁏ Δ , B ⌉

  ⟨_⟩ : ∀ {Δ Γ A} → A ∈ Γ → A [∈] ⌈ Γ ⁏ Δ ⌉
  ⟨_⟩ {Δ} top     = lemᵢ {Δ}
  ⟨_⟩ {Δ} (pop i) = lemᵢᵢ {Δ} ⟨ i ⟩

  m⟨_⟩ : ∀ {Γ Δ A} → A ∈ Δ → A [m∈] ⌈ Γ ⁏ Δ ⌉
  m⟨_⟩ {Γ} top     = lemₘ {Γ}
  m⟨_⟩ {Γ} (pop i) = lemₘₘ {Γ} (m⟨_⟩ {Γ} i)

  postulate
    lem₄ : ∀ {A Γ Δ}   → ⌈ Γ ⁏ Δ ⌉ [,] A ≡ ⌈ Γ , A ⁏ Δ ⌉
    lem₅ : ∀ {A Γ Δ}   → ⌈ Γ ⁏ Δ ⌉ [m,] A ≡ ⌈ Γ ⁏ Δ , A ⌉
    lem₆ : ∀ {Δ A B Γ} → ⌈ Γ , A ⁏ Δ ⌉ [⊢] B → ⌈ Γ ⁏ Δ ⌉ [,] A [⊢] B
    lem₇ : ∀ {Γ A C Δ} → ⌈ Γ ⁏ Δ , A ⌉ [⊢] C → ⌈ Γ ⁏ Δ ⌉ [m,] A [⊢] C
    lem₈ : ∀ {Γ A Δ}   → ⌈ ∅ ⁏ Δ ⌉ [⊢] A → ⌊ ⌈ Γ ⁏ Δ ⌉ ⌋ [⊢] A

  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → ⌈ Γ ⁏ Δ ⌉ [⊢] A
  [ var i ]             = [var] ⟨ i ⟩
  [ lam {Δ = Δ} t ]     = [lam] (lem₆ {Δ} [ t ])
  [ app t u ]           = [app] [ t ] [ u ]
  [ mvar {Γ = Γ} i ]    = [mvar] (m⟨_⟩ {Γ} i)
  [ box {Γ = Γ} t ]     = [box] (lem₈ {Γ} [ t ])
  [ unbox {Γ = Γ} t u ] = [unbox] [ t ] (lem₇ {Γ} [ u ])
  [ pair t u ]          = [pair] [ t ] [ u ]
  [ fst t ]             = [fst] [ t ]
  [ snd t ]             = [snd] [ t ]
  [ unit ]              = [unit]

--  [mlam] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A [⊢] B → Γ ⁏ Δ [⊢] □ A ▻ B
--  [mlam] t = [lam] ([unbox] ([var] top) (mono[⊢] (weak⊆ , refl⊆) t))

--   [mmulticut₀] : ∀ {Ξ A Γ Δ} → ∅ ⁏ Δ [⊢]⋆ Ξ → Γ ⁏ Ξ [⊢] A → Γ ⁏ Δ [⊢] A
--   [mmulticut₀] {∅}     ∙        u = mono²[⊢] (refl⊆ , bot⊆) u
--   [mmulticut₀] {Ξ , B} (ts , t) u = [app] ([mmulticut₀] ts ([mlam] u)) ([box] t)

--  [mlam] : ∀ {Γ A B Δ} → ⌈ Γ ⁏ Δ , A ⌉ [⊢] B → ⌈ Γ ⁏ Δ ⌉ [⊢] □ A ▻ B
--  [mlam] t = [lam] ([unbox] ([var] ⟨ top ⟩) (mono[⊢] {!!} t))
--
  postulate
    bla₁ : ∀ {Γ Δ} → ⌈ Γ ⁏ ∅ ⌉ ≤ ⌈ Γ ⁏ Δ ⌉
    bla₂ : ∀ {Γ Δ A} → ⌈ ∅ ⁏ Δ ⌉ [⊢] A → ⌊ ⌈ Γ ⁏ Δ ⌉ ⌋ [⊢] A
    ble₁ : ∀ {w : World} → [∅] ≤ ⌊ w ⌋
    ble₂ : ∀ {A} {w : World} → ⌊ w ⌋ [⊢] A → ⌊ ⌊ w ⌋ ⌋ [⊢] A
--
--  [mhmm] : ∀ {Ξ Γ Δ A} → ⌈ ∅ ⁏ Δ ⌉ [⊢]⋆ Ξ → ⌈ Γ ⁏ Ξ ⌉ [⊢] A → ⌈ Γ ⁏ Δ ⌉ [⊢] A
--  [mhmm] {∅}     {Γ} {Δ} ∙        u = mono[⊢] (ugh₁ {Γ}) u
-- [mhmm] {Ξ , B} {Γ} {Δ} (ts , t) u = [app] ([mhmm] {Γ = Γ} ts ([mlam] {Γ} u)) ([box] (ugh₂ {Γ} t))



  ugh₁ : ∀ {Δ} {w : World} {A} → ⌊ w ⌋ [⊢]⋆ Δ → ⌈ ∅ ⁏ Δ ⌉ [⊢] A → ⌊ w ⌋ [⊢] A
  ugh₁ {∅}     {w} ∙        u = {!!} -- mono[⊢] ble₁ u
  ugh₁ {Δ , B} {w} (ts , t) u = [unbox] ([box] (ble₂ t)) {!u!}

-- -- Soundness with respect to all models, or evaluation.

module _ {{_ : Model}} where
  cor₁ : ∀ {w w′ : World} → ⌊ w ⌋ ≤ ⌊ w′ ⌋ → ⌊ w ⌋ ≤ ⌊ ⌊ w′ ⌋ ⌋
  cor₁ ξ = trans≤ ξ lem₂


eval : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ ד δ = lookup i γ
eval (lam {A} {B} t)     γ ד δ = return {A ▻ B} λ ξ a →
                                   eval t (mono⊩⋆ ξ γ , a)
                                          (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
                                          (mono⊩⋆ (≤→⌊≤⌋ ξ) δ)
eval (app {A} {B} t u)   γ ד δ = bind {A ▻ B} {B} (eval t γ ד δ) λ ξ f →
                                   _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ ξ γ)
                                                           (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
                                                           (mono⊩⋆ (≤→⌊≤⌋ ξ) δ))
eval (mvar {A} i)        γ ד δ = mono⊩ {A} lem₁ (lookup i δ)
eval {Γ} {Δ} (box {A} t) γ ד δ = return {□ A} λ ζ →
                                   let ד′ = mono[⊢]⋆ (R→⌊≤⌋ ζ) ד
                                       t′ = [ t ]
                                   in  {!!} ⅋ -- ugh₁ ד′ t′ ⅋
                                     eval t ∙
                                            (mono[⊢]⋆ (cor₁ (R→⌊≤⌋ ζ)) ד)
                                            (mono⊩⋆ (cor₁ (R→⌊≤⌋ ζ)) δ)
eval (unbox {A} {C} t u) γ ד δ = bind {□ A} {C} (eval t γ ד δ) λ ξ a →
                                   eval u (mono⊩⋆ ξ γ)
                                          (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד , syn (a reflR))
                                          (mono⊩⋆ (≤→⌊≤⌋ ξ) δ , sem (a reflR))
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
      { World    = Cx² Ty Ty
      ; _≤_      = _⊆²_
      ; refl≤    = refl⊆²
      ; trans≤   = trans⊆²
      ; _R_      = λ { (Γ ⁏ Δ) (Γ′ ⁏ Δ′) → Δ ⊆ Δ′ }
      ; reflR    = refl⊆
      ; transR   = trans⊆
      ; ≤⨾R→R   = λ { (w′ , ((η , θ) , θ′)) → trans⊆ θ θ′ }
      ; ⌊_⌋      = λ { (Γ ⁏ Δ) → ∅ ⁏ Δ }
      ; ≤→⌊≤⌋   = λ { (η , θ) → refl⊆ , θ }
      ; R→⌊≤⌋   = λ θ → refl⊆ , θ
      ; lem₁     = bot⊆ , refl⊆
      ; lem₂     = refl⊆²
      ; lem₃     = refl⊆²
      ; [∅]      = ∅ ⁏ ∅
      ; _[,]_    = λ { (Γ ⁏ Δ) A → Γ , A ⁏ Δ }
      ; _[m,]_   = λ { (Γ ⁏ Δ) A → Γ ⁏ Δ , A }
      ; _[∈]_    = λ { A (Γ ⁏ Δ) → A ∈ Γ }
      ; _[m∈]_   = λ { A (Γ ⁏ Δ) → A ∈ Δ }
      ; _[⊢]_   = _⊢_
      ; mono[⊢] = mono²⊢
      ; [var]    = var
      ; [lam]    = lam
      ; [app]    = app
      ; [mvar]   = mvar
      ; [box]    = box
      ; [unbox]  = unbox
      ; [pair]   = pair
      ; [fst]    = fst
      ; [snd]    = snd
      ; [unit]   = unit
      ; _[⊢ⁿᶠ]_ = _⊢ⁿᶠ_
      ; _⊪ᵅ_    = λ { (Γ ⁏ Δ) P → Γ ⁏ Δ ⊢ⁿᵉ α P }
      ; mono⊪ᵅ  = mono²⊢ⁿᵉ
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

mrefl₀[⊢]⋆ : ∀ {Δ} → ∅ ⁏ Δ [⊢]⋆ Δ
mrefl₀[⊢]⋆ {∅}     = ∙
mrefl₀[⊢]⋆ {Δ , A} = mono[⊢]⋆ (refl⊆ , weak⊆) mrefl₀[⊢]⋆ , [mvar] top

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
