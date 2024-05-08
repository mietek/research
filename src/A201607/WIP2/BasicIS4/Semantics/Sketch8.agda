-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Kripke-style semantics with exploding abstract worlds, and glueing for □ only.

module A201607.WIP2.BasicIS4.Semantics.Sketch8 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


-- Intuitionistic modal Kripke-CPS models, with exploding worlds.

record Model : Set₁ where
  infix 3 _⊪ᵅ_ _[⊢]_ _[⊢ⁿᶠ]_
  infix 5 _≤_
  infixl 5 _[+]_
  infix 3 _[∈]_

  field
    World : Set

    -- TODO
    [∅]    : World

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    -- bot≤   : ∀ {w} → [∅] ≤ w

    -- Modal accessibility; preorder.
    -- _R_    : World → World → Set
    -- reflR  : ∀ {w} → w R w
    -- transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- TODO
    -- ⌊_⌋    : World → World
    -- lem₁   : ∀ {w} → ⌊ w ⌋ ≤ w
    -- lem₂   : ∀ {w} → ⌊ w ⌋ ≤ ⌊ ⌊ w ⌋ ⌋
    -- ≤→⌊≤⌋ : ∀ {w w′} → w ≤ w′ → ⌊ w ⌋ ≤ ⌊ w′ ⌋

    -- TODO
    _[+]_  : World → Cx² Ty Ty → World
    _[∈]_  : Cx² Ty Ty → World → Set
--    [top]  : ∀ {A w}   → A [∈] w [,] A
--    [mtop] : ∀ {A w}   → A [m∈] w [m,] A
--    [pop]  : ∀ {A B w} → A [∈] w → A [∈] w [,] B
--    [mpop] : ∀ {A B w} → A [m∈] w → A [m∈] w [m,] B

    -- Gentzen-style syntax; monotonic.
    _[⊢]_   : World → Ty → Set
    mono[⊢] : ∀ {A w w′} → w ≤ w′ → w [⊢] A → w′ [⊢] A
    [var]    : ∀ {A w}   → (∅ , A ⁏ ∅) [∈] w → w [⊢] A
    [lam]    : ∀ {A B w} → w [+] (∅ , A ⁏ ∅) [⊢] B → w [⊢] A ▻ B
    [app]    : ∀ {A B w} → w [⊢] A ▻ B → w [⊢] A → w [⊢] B
    [mvar]   : ∀ {A w}   → (∅ ⁏ ∅ , A) [∈] w → w [⊢] A
    [box]    : ∀ {Γ Δ A} → [∅] [+] (∅ ⁏ Δ) [⊢] A → [∅] [+] (Γ ⁏ Δ) [⊢] □ A
    [unbox]  : ∀ {A C w} → w [⊢] □ A → w [+] (∅ ⁏ ∅ , A) [⊢] C → w [⊢] C
    [pair]   : ∀ {A B w} → w [⊢] A → w [⊢] B → w [⊢] A ∧ B
    [fst]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] A
    [snd]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] B
    [unit]   : ∀ {w}     → w [⊢] ⊤

    -- Syntax in normal form.
    _[⊢ⁿᶠ]_ : World → Ty → Set

    -- Strong forcing for atomic propositions; monotonic.
    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

--  infixl 5 _[,]⋆_
--  _[,]⋆_ : World → Cx Ty → World
--  w [,]⋆ ∅       = w
--  w [,]⋆ (Ξ , A) = w [,]⋆ Ξ [,] A
--
--  infixl 5 _[m,]⋆_
--  _[m,]⋆_ : World → Cx Ty → World
--  w [m,]⋆ ∅       = w
--  w [m,]⋆ (Ξ , A) = w [m,]⋆ Ξ [m,] A

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
    w ⊪ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
--    w ⊪ □ A   = ∀ {w′} → ⌊ w ⌋ ≤ ⌊ w′ ⌋ → Glue (⌊ w′ ⌋ [⊢] A) (⌊ w′ ⌋ ⊩ A)
    w ⊪ □ A   = ∀ {Ξ} → Glue ([∅] [+] Ξ [⊢] A) ([∅] [+] Ξ ⊩ A)
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
--    mono⊪ {□ A}   ξ s = λ ζ → s (trans≤ (≤→⌊≤⌋ ξ) ζ)
    mono⊪ {□ A}   ξ s = s
    mono⊪ {A ∧ B} ξ s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
    mono⊪ {⊤}    ξ s = ∙

    mono⊩ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

  mono⊩⋆ : ∀ {Ξ} {w w′ : World} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Ξ , A} ξ (γ , a) = mono⊩⋆ {Ξ} ξ γ , mono⊩ {A} ξ a


-- TODO: unfinished


-- -- Additional useful equipment.

-- module _ {{_ : Model}} where
--   _⟪$⟫_ : ∀ {A B w} → w ⊪ A ▻ B → w ⊩ A → w ⊩ B
--   s ⟪$⟫ a = s refl≤ a

--   return : ∀ {A w} → w ⊪ A → w ⊩ A
--   return {A} a = λ ξ k → k refl≤ (mono⊪ {A} ξ a)

--   bind : ∀ {A B w} → w ⊩ A → (∀ {w′} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
--   bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans≤ ξ ξ′) a′ refl≤ (λ ξ″ a″ → k′ (trans≤ ξ′ ξ″) a″))


-- -- Entailment, or forcing in all worlds of all models, for sequents.

-- infix 3 _⊨_
-- _⊨_ : Cx² Ty Ty → Ty → Set₁
-- Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩ A

-- infix 3 _⊨⋆_
-- _⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
-- Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩⋆ Ξ


-- -- Additional useful equipment, for sequents.

-- module _ {{_ : Model}} where
--   lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
--   lookup top     (γ , a) = a
--   lookup (pop i) (γ , b) = lookup i γ


-- --


-- open import BasicIS4.Syntax.DyadicGentzenNormalForm public


-- -- Internalisation of syntax as syntax representation in a particular model.

-- module _ {{_ : Model}} where
-- --  [_]ᶜˣ : Cx² Ty Ty → World
-- --  [ ∅ ⁏ ∅ ]ᶜˣ         = [∅]
-- --  [ Γ , A ⁏ ∅ ]ᶜˣ     = [ Γ ⁏ ∅ ]ᶜˣ [,] A
-- --  [ ∅ ⁏ Δ , B ]ᶜˣ     = [ ∅ ⁏ Δ ]ᶜˣ [m,] B
-- --  [ Γ , A ⁏ Δ , B ]ᶜˣ = [ Γ ⁏ Δ ]ᶜˣ [,] A [m,] B

-- --  mel₃ : ∀ {Γ Δ A} → [ Γ , A ⁏ Δ ]ᶜˣ ≡ [ Γ ⁏ Δ ]ᶜˣ [,] A
-- --  mel₃ {∅}     = {!!}
-- --  mel₃ {Γ , B} = {!!}
-- --
-- --  lem₃ : ∀ {Δ A C Γ} → [ Γ , A ⁏ Δ ]ᶜˣ [⊢] C → [ Γ ⁏ Δ ]ᶜˣ [,] A [⊢] C
-- --  lem₃ t = {!!}
-- --
-- --  postulate
-- --    lem₄ : ∀ {Γ A Δ}   → [ ∅ ⁏ Δ ]ᶜˣ [⊢] A → ⌊ [ Γ ⁏ Δ ]ᶜˣ ⌋ [⊢] A
-- --    lem₅ : ∀ {Γ A C Δ} → [ Γ ⁏ Δ , A ]ᶜˣ [⊢] C → [ Γ ⁏ Δ ]ᶜˣ [m,] A [⊢] C
-- --
-- --  [_]ⁱˣ : ∀ {A Γ Δ} → A ∈ Γ → A [∈] [ Γ ⁏ Δ ]ᶜˣ
-- --  [ top ]ⁱˣ   = {![top]!}
-- --  [ pop i ]ⁱˣ = {!!}
-- --
-- --  m[_]ⁱˣ : ∀ {Γ A Δ} → A ∈ Δ → A [m∈] [ Γ ⁏ Δ ]ᶜˣ
-- --  m[ top ]ⁱˣ   = {!!}
-- --  m[ pop i ]ⁱˣ = {!!}
-- --
-- --  [_] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → [ Γ ⁏ Δ ]ᶜˣ [⊢] A
-- --  [ var i ]             = [var] [ i ]ⁱˣ
-- --  [ lam {Δ = Δ} t ]     = [lam] (lem₃ {Δ} [ t ])
-- --  [ app t u ]           = [app] [ t ] [ u ]
-- --  [ mvar {Γ = Γ} i ]    = [mvar] (m[_]ⁱˣ {Γ} i)
-- --  [ box {Γ = Γ} t ]     = [box] (lem₄ {Γ} [ t ])
-- --  [ unbox {Γ = Γ} t u ] = [unbox] [ t ] (lem₅ {Γ} [ u ])
-- --  [ pair t u ]          = [pair] [ t ] [ u ]
-- --  [ fst t ]             = [fst] [ t ]
-- --  [ snd t ]             = [snd] [ t ]
-- --  [ unit ]              = [unit]
-- --
-- --  [box]⋆ : ∀ {Ξ w} → ⌊ w ⌋ [⊢]⋆ Ξ → w [⊢]⋆ □⋆ Ξ
-- --  [box]⋆ {∅}     ∙        = ∙
-- --  [box]⋆ {Ξ , A} (ts , t) = [box]⋆ ts , [box] t

-- --  postulate
-- --    lem₆ : ∀ {Ξ C w} → w [⊢] C → w [m,]⋆ Ξ [⊢] C
-- --    lem₇ : ∀ {Ξ A C w} → w [m,]⋆ (Ξ , A) [⊢] C → (w [m,]⋆ Ξ) [m,] A [⊢] C
-- --
-- --  [unbox]⋆ : ∀ {Ξ C w} → w [⊢]⋆ □⋆ Ξ → w [m,]⋆ Ξ [⊢] C → w [⊢] C
-- --  [unbox]⋆ {∅}     ∙        u = u
-- --  [unbox]⋆ {Ξ , A} (ts , t) u = [unbox]⋆ ts ([unbox] (lem₆ {Ξ} t) (lem₇ {Ξ} u))
-- --
-- --  mlet : ∀ {A C w} → ⌊ w ⌋ [⊢] A → w [m,] A [⊢] C → w [⊢] C
-- --  mlet t u = [unbox] ([box] t) u
-- --
-- --  mlet⋆ : ∀ {Ξ C w} → ⌊ w ⌋ [⊢]⋆ Ξ → w [m,]⋆ Ξ [⊢] C → w [⊢] C
-- --  mlet⋆ ts u = [unbox]⋆ ([box]⋆ ts) u

--   -- [unbox]  : ∀ {A C w} → w [⊢] □ A → w [m,] A [⊢] C → w [⊢] C



-- --  help : ∀ {Ξ w A} → w [⊢] □ A → w [m,]⋆ Ξ [⊢] □ A
-- --  help = {!!}
-- --
-- --  unbox′ : ∀ {Ξ A C w} → w [⊢] □ A → [∅] [m,]⋆ Ξ [m,] A [⊢] C → [∅] [m,]⋆ Ξ [⊢] C
-- --  unbox′ = {!!}
-- --
-- --  [unbox]⋆ : ∀ {Ξ C w} → w [⊢]⋆ □⋆ Ξ → [∅] [m,]⋆ Ξ [⊢] C → [∅] [⊢] C
-- --  [unbox]⋆ {∅}     ∙        u = u
-- --  [unbox]⋆ {Ξ , A} (ts , t) u = [unbox]⋆ ts (unbox′ {Ξ} t u)


-- --  [box]⋆ : ∀ {Ξ w} → ⌊ w ⌋ [⊢]⋆ Ξ → w [⊢]⋆ □⋆ Ξ
-- --  [box]⋆ {∅}     ∙        = ∙
-- --  [box]⋆ {Ξ , A} (ts , t) = [box]⋆ ts , [box] t

--   [box]⋆ : ∀ {Ξ w} → ⌊ w ⌋ [⊢]⋆ Ξ → ⌊ w ⌋ [⊢]⋆ □⋆ Ξ
--   [box]⋆ {∅}     ∙        = ∙
--   [box]⋆ {Ξ , A} (ts , t) = [box]⋆ ts , [box] t

-- --  postulate
-- --    wtf : ∀ {Ξ A w} → w [⊢] □ A → ⌊ w ⌋ [m,]⋆ Ξ [⊢] □ A
-- --
-- --  [unbox]⋆ : ∀ {Ξ C w} → w [⊢]⋆ □⋆ Ξ → ⌊ w ⌋ [m,]⋆ Ξ [⊢] C → ⌊ w ⌋ [⊢] C
-- --  [unbox]⋆ {∅}     ∙        u = u
-- --  [unbox]⋆ {Ξ , A} (ts , t) u = [unbox]⋆ ts ([unbox] (wtf {Ξ} t) u)
-- --
-- --  omg : ∀ {Ξ C w} → ⌊ w ⌋ [⊢]⋆ Ξ → ⌊ w ⌋ [m,]⋆ Ξ [⊢] C → ⌊ w ⌋ [⊢] C
-- --  omg ts u = [unbox]⋆ ([box]⋆ ts) u

-- {-
--   postulate
--     [top] : ∀ {A w} → A [∈] w [,] A
--     foo   : ∀ {A w} → w ≤ (w [,] A)
--     mfoo  : ∀ {A w} → w ≤ (w [m,] A)

--   postulate
--     lemᵛᵃʳ   : ∀ {Γ Δ A w}   → A ∈ Γ → A [∈] w [,]⋆ Γ [m,]⋆ Δ

--     lemˡᵃᵐ   : ∀ {Γ Δ A B w} → w [,]⋆ (Γ , A) [m,]⋆ Δ [⊢] B
--                              → w [,]⋆ Γ [m,]⋆ Δ [,] A [⊢] B

--     lemᵐᵛᵃʳ  : ∀ {Γ Δ A w}   → A ∈ Δ → A [m∈] w [,]⋆ Γ [m,]⋆ Δ

--     lemᵇᵒˣ   : ∀ {Γ Δ A w}   → w [,]⋆ ∅ [m,]⋆ Δ [⊢] A
--                              → ⌊ w [,]⋆ Γ [m,]⋆ Δ ⌋ [⊢] A

--     lemᵘⁿᵇᵒˣ : ∀ {Γ Δ A C w} → w [,]⋆ Γ [m,]⋆ (Δ , A) [⊢] C
--                              → w [,]⋆ Γ [m,]⋆ Δ [m,] A [⊢] C

--   wtf : ∀ {Ξ A C w} → ⌊ w ⌋ [m,]⋆ (Ξ , A) [⊢] C → ⌊ w ⌋ [m,]⋆ Ξ [⊢] □ A ▻ C
--   wtf t = [lam] ([unbox] ([var] [top]) (mono[⊢] {!!} t))

--   omg : ∀ {Ξ C w} → ⌊ w ⌋ [⊢]⋆ □⋆ Ξ → ⌊ w ⌋ [m,]⋆ Ξ [⊢] C → ⌊ w ⌋ [⊢] C
--   omg {∅}     ∙        u = u
--   omg {Ξ , A} (ts , t) u = [app] (omg ts (wtf {Ξ} u)) t

--   [_] : ∀ {A Γ Δ w} → Γ ⁏ Δ ⊢ A → w [,]⋆ Γ [m,]⋆ Δ [⊢] A
--   [ var {Γ = Γ} {Δ} i ]     = [var] (lemᵛᵃʳ {Γ} {Δ} i)
--   [ lam {Γ = Γ} {Δ} t ]     = [lam] (lemˡᵃᵐ {Γ} {Δ} [ t ])
--   [ app t u ]               = [app] [ t ] [ u ]
--   [ mvar {Γ = Γ} {Δ} i ]    = [mvar] (lemᵐᵛᵃʳ {Γ} {Δ} i)
--   [ box {Γ = Γ} {Δ} t ]     = mono[⊢] lem₁ ([box] (lemᵇᵒˣ {Γ} {Δ} [ t ]))
--   [ unbox {Γ = Γ} {Δ} t u ] = [unbox] [ t ] (lemᵘⁿᵇᵒˣ {Γ} {Δ} [ u ])
--   [ pair t u ]              = [pair] [ t ] [ u ]
--   [ fst t ]                 = [fst] [ t ]
--   [ snd t ]                 = [snd] [ t ]
--   [ unit ]                  = [unit]
-- -}


-- -- Soundness with respect to all models, or evaluation.

-- eval : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
-- eval (var i)             γ ד δ = lookup i γ
-- eval (lam {A} {B} t)     γ ד δ = return {A ▻ B} λ ξ a →
--                                    eval t (mono⊩⋆ ξ γ , a)
--                                           (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
--                                           (mono⊩⋆ (≤→⌊≤⌋ ξ) δ)
-- eval (app {A} {B} t u)   γ ד δ = bind {A ▻ B} {B} (eval t γ ד δ) λ ξ f →
--                                    _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ ξ γ)
--                                                            (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
--                                                            (mono⊩⋆ (≤→⌊≤⌋ ξ) δ))
-- eval (mvar {A} i)        γ ד δ = mono⊩ {A} lem₁ (lookup i δ)
-- eval {Γ} {Δ} (box {A} t) γ ד δ = return {□ A} λ ζ →
--                                    let ד′ = mono[⊢]⋆ ζ ד
--                                        t′ = {!!}
--                                    in  {!omg ([box]⋆ ד′) t′!} ⅋
--                                          eval t ∙
--                                             (mono[⊢]⋆ (trans≤ ζ lem₂) ד)
--                                             (mono⊩⋆ (trans≤ ζ lem₂) δ)
-- eval (unbox {A} {C} t u) γ ד δ = bind {□ A} {C} (eval t γ ד δ) λ ξ a →
--                                    eval u (mono⊩⋆ ξ γ)
--                                           (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד , syn (a refl≤))
--                                           (mono⊩⋆ (≤→⌊≤⌋ ξ) δ , sem (a refl≤))
-- eval (pair {A} {B} t u)  γ ד δ = return {A ∧ B} (eval t γ ד δ , eval u γ ד δ)
-- eval (fst {A} {B} t)     γ ד δ = bind {A ∧ B} {A} (eval t γ ד δ) (K π₁)
-- eval (snd {A} {B} t)     γ ד δ = bind {A ∧ B} {B} (eval t γ ד δ) (K π₂)
-- eval unit                γ ד δ = return {⊤} ∙

-- eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
-- eval⋆ {∅}     ∙        γ ד δ = ∙
-- eval⋆ {Ξ , A} (ts , t) γ ד δ = eval⋆ ts γ ד δ , eval t γ ד δ


-- -- The canonical model.

-- private
--   instance
--     canon : Model
--     canon = record
--       { World    = Cx² Ty Ty
--       ; [∅]      = ∅ ⁏ ∅
--       ; _≤_      = _⊆²_
--       ; refl≤    = refl⊆²
--       ; trans≤   = trans⊆²
--       ; bot≤     = bot⊆²
--       ; ⌊_⌋      = λ { (Γ ⁏ Δ) → ∅ ⁏ Δ }
--       ; lem₁     = bot⊆ , refl⊆
--       ; lem₂     = refl⊆²
--       ; ≤→⌊≤⌋   = λ { (η , θ) → refl⊆ , θ }
--       ; _[+]_    = λ { (Γ ⁏ Δ) (Γ′ ⁏ Δ′) → Γ ⧺ Γ′ ⁏ Δ ⧺ Δ′ }
-- --      ; _[,]_    = λ { (Γ ⁏ Δ) A → Γ , A ⁏ Δ }
-- --      ; _[m,]_   = λ { (Γ ⁏ Δ) A → Γ ⁏ Δ , A }
--       ; _[∈]_    = λ { A (Γ ⁏ Δ) → A ∈ Γ }
--       ; _[m∈]_   = λ { A (Γ ⁏ Δ) → A ∈ Δ }
--       ; _[⊢]_   = _⊢_
--       ; mono[⊢] = mono²⊢
--       ; [var]    = var
--       ; [lam]    = lam
--       ; [app]    = app
--       ; [mvar]   = mvar
--       ; [box]    = box
--       ; [unbox]  = unbox
--       ; [pair]   = pair
--       ; [fst]    = fst
--       ; [snd]    = snd
--       ; [unit]   = unit
--       ; _[⊢ⁿᶠ]_ = _⊢ⁿᶠ_
--       ; _⊪ᵅ_    = λ { (Γ ⁏ Δ) P → Γ ⁏ Δ ⊢ⁿᵉ α P }
--       ; mono⊪ᵅ  = mono²⊢ⁿᵉ
--       }


-- -- Soundness and completeness with respect to the canonical model.

-- module _ {U : Set} where
--   grab∈ : ∀ {A : U} {Γ Γ′} → Γ , A ⊆ Γ′ → A ∈ Γ′
--   grab∈ (skip η) = pop (grab∈ η)
--   grab∈ (keep η) = top

-- mutual
--   reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
--   reifyᶜ {α P}   k = k refl⊆² λ ξ s → neⁿᶠ s
--   reifyᶜ {A ▻ B} k = k refl⊆² λ ξ s → lamⁿᶠ (reifyᶜ (s weak⊆²₁ (reflectᶜ {A} (varⁿᵉ top))))
--   reifyᶜ {□ A}   k = k refl⊆² λ {w} ξ s → boxⁿᶠ (syn (s {w} refl⊆²))
--   reifyᶜ {A ∧ B} k = k refl⊆² λ ξ s → pairⁿᶠ (reifyᶜ (π₁ s)) (reifyᶜ (π₂ s))
--   reifyᶜ {⊤}    k = k refl⊆² λ ξ s → unitⁿᶠ

--   reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
--   reflectᶜ {α P}   t = return {α P} t
--   reflectᶜ {A ▻ B} t = return {A ▻ B} λ { (η , θ) a →
--                          reflectᶜ {B} (appⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (reifyᶜ a)) }
--   reflectᶜ {□ A}   t = λ { (η , θ) k →
--                          neⁿᶠ (unboxⁿᵉ (mono²⊢ⁿᵉ (η , θ) t) (k (refl⊆ , weak⊆) λ { (η′ , θ′) →
--                            mvar (grab∈ θ′) ⅋
--                              reflectᶜ {A} (mvarⁿᵉ (grab∈ θ′)) } )) }
--   reflectᶜ {A ∧ B} t = return {A ∧ B} (reflectᶜ (fstⁿᵉ t) , reflectᶜ (sndⁿᵉ t))
--   reflectᶜ {⊤}    t = return {⊤} ∙

-- reifyᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊩⋆ Ξ → Γ ⁏ Δ ⊢⋆ⁿᶠ Ξ
-- reifyᶜ⋆ {∅}     ∙        = ∙
-- reifyᶜ⋆ {Ξ , A} (ts , t) = reifyᶜ⋆ ts , reifyᶜ t

-- reflectᶜ⋆ : ∀ {Ξ Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ ⁏ Δ ⊩⋆ Ξ
-- reflectᶜ⋆ {∅}     ∙        = ∙
-- reflectᶜ⋆ {Ξ , A} (ts , t) = reflectᶜ⋆ ts , reflectᶜ t


-- -- Reflexivity.

-- refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
-- refl⊩⋆ = reflectᶜ⋆ refl⊢⋆ⁿᵉ

-- mrefl₀[⊢]⋆ : ∀ {Δ} → ∅ ⁏ Δ [⊢]⋆ Δ
-- mrefl₀[⊢]⋆ {∅}     = ∙
-- mrefl₀[⊢]⋆ {Δ , A} = mono[⊢]⋆ (refl⊆ , weak⊆) mrefl₀[⊢]⋆ , mvar top

-- mrefl₀⊢⋆ⁿᵉ : ∀ {Δ} → ∅ ⁏ Δ ⊢⋆ⁿᵉ Δ
-- mrefl₀⊢⋆ⁿᵉ {∅}     = ∙
-- mrefl₀⊢⋆ⁿᵉ {Γ , A} = mmono⊢⋆ⁿᵉ weak⊆ mrefl₀⊢⋆ⁿᵉ , mvarⁿᵉ top

-- mrefl₀⊩⋆ : ∀ {Δ} → ∅ ⁏ Δ ⊩⋆ Δ
-- mrefl₀⊩⋆ = reflectᶜ⋆ mrefl₀⊢⋆ⁿᵉ


-- -- Completeness with respect to all models, or quotation.

-- quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
-- quot s = reifyᶜ (s refl⊩⋆ mrefl₀[⊢]⋆ mrefl₀⊩⋆)


-- -- Normalisation by evaluation.

-- norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
-- norm = quot ∘ eval
