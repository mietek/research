module A202104.PD where

open import A202103.Prelude public
open import A202103.List public
open import A202103.GenericRenaming public
open import A202104.Semantics public

------------------------------------------------------------------------------

infixr 7 _⊃_
data Type : Set where
  α_  : ∀ (P : Atom) → Type
  _⊃_ : ∀ (A B : Type) → Type
  □_  : ∀ (A : Type) → Type
  ◇_  : ∀ (A : Type) → Type

record TrueAss : Set where
  constructor _true
  field
    A : Type

record ValidAss : Set where
  constructor _valid
  field
    A : Type

TrueCtx = List TrueAss

ValidCtx = List ValidAss

-- NOTE: Both syntaxes come from Pfenning-Davies.
-- https://github.com/dpndnt/library/blob/master/doc/pdf/pfenning-davies-2001.pdf

module ImplicitSyntax where
  mutual
    infix 3 _⁏_⊢_true
    data _⁏_⊢_true (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      var    : ∀ {A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊢ A true
      lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B true → Δ ⁏ Γ ⊢ A ⊃ B true
      app    : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B true → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ B true
      vvar   : ∀ {A} (x : Δ ∋ A valid) → Δ ⁏ Γ ⊢ A true
      box    : ∀ {A} → Δ ⁏ · ⊢ A true → Δ ⁏ Γ ⊢ □ A true
      letbox : ∀ {A C} → Δ ⁏ Γ ⊢ □ A true → Δ , A valid ⁏ Γ ⊢ C true → Δ ⁏ Γ ⊢ C true
      pdia   : ∀ {A} → Δ ⁏ Γ ⊢ A poss → Δ ⁏ Γ ⊢ ◇ A true

    infix 3 _⁏_⊢_poss
    data _⁏_⊢_poss (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      retp    : ∀ {A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ A poss
      letboxp : ∀ {A C} → Δ ⁏ Γ ⊢ □ A true → Δ , A valid ⁏ Γ ⊢ C poss → Δ ⁏ Γ ⊢ C poss
      letdiap : ∀ {A C} → Δ ⁏ Γ ⊢ ◇ A true → Δ ⁏ · , A true ⊢ C poss → Δ ⁏ Γ ⊢ C poss

  postulate
    monoTrue₁ : ∀ {Δ Δ′ Γ A} → Δ′ ⊒ Δ → Δ ⁏ Γ ⊢ A true → Δ′ ⁏ Γ ⊢ A true
  --monoTrue₁ η t = {!!}

    monoTrue₂ : ∀ {Δ Γ Γ′ A} → Γ′ ⊒ Γ → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ′ ⊢ A true
  --monoTrue₂ η t = {!!}

    monoPoss₁ : ∀ {Δ Δ′ Γ A} → Δ′ ⊒ Δ → Δ ⁏ Γ ⊢ A poss → Δ′ ⁏ Γ ⊢ A poss
  --monoPoss₁ η t = {!!}

    monoPoss₂ : ∀ {Δ Γ Γ′ A} → Γ′ ⊒ Γ → Δ ⁏ Γ ⊢ A poss → Δ ⁏ Γ′ ⊢ A poss
  --monoPoss₂ η t = {!!}

  law-unbox : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ □ A ⊃ A true
  law-unbox = lam (letbox (var top) (vvar top))

  law-rebox : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ □ A ⊃ □ □ A true
  law-rebox = lam (letbox (var top) (box (box (vvar top))))

  law-mapbox : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ (□ A ⊃ □ B) true
  law-mapbox = lam (lam (letbox (var (pop top)) (letbox (var top) (box (app (vvar (pop top)) (vvar top))))))

  law-dia : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A ⊃ ◇ A true
  law-dia = lam (pdia (retp (var top)))

  law-undia : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ ◇ ◇ A ⊃ ◇ A true
  law-undia = lam (pdia (letdiap (var top) (letdiap (var top) (retp (var top)))))

  law-mapdia : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ (◇ A ⊃ ◇ B) true
  law-mapdia = lam (lam (letbox (var (pop top)) (pdia (letdiap (var top) (retp (app (vvar top) (var top)))))))

  unbox : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ □ A true → Δ ⁏ Γ ⊢ A true
  unbox t = app law-unbox t

  rebox : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ □ A true → Δ ⁏ Γ ⊢ □ □ A true
  rebox t = app law-rebox t

  mapbox : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ □ (A ⊃ B) true → Δ ⁏ Γ ⊢ □ A true → Δ ⁏ Γ ⊢ □ B true
  mapbox t u = app (app law-mapbox t) u

  dia : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ ◇ A true
  dia t = app law-dia t

  undia : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ ◇ ◇ A true → Δ ⁏ Γ ⊢ ◇ A true
  undia t = app law-undia t

  mapdia : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ □ (A ⊃ B) true → Δ ⁏ Γ ⊢ ◇ A true → Δ ⁏ Γ ⊢ ◇ B true
  mapdia t u = app (app law-mapdia t) u

  _⇒_ : Type → Type → Type
  A ⇒ B = □ A ⊃ B

  llam : ∀ {Δ Γ A B} → Δ , A valid ⁏ Γ ⊢ B true → Δ ⁏ Γ ⊢ A ⇒ B true
  llam t = lam (letbox (var top) (monoTrue₂ (wkr idr) t))

  lapp : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ A ⇒ B true → Δ ⁏ · ⊢ A true → Δ ⁏ Γ ⊢ B true
  lapp t₁ t₂ = app t₁ (box t₂)

  ○_ : Type → Type
  ○ A = ◇ □ A

  cir : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ □ A poss → Δ ⁏ Γ ⊢ ○ A true
  cir t = pdia t

  letcir : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊢ ○ A true → Δ , A valid ⁏ · ⊢ □ B poss → Δ ⁏ Γ ⊢ □ B poss
  letcir t₁ t₂ = letdiap t₁ (letboxp (var top) (monoPoss₂ (wkr idr) t₂))

-- NOTE: This syntax is a variant with explicit derivations for validity.
-- This clarifies the connection between the syntax and the semantics.

module ExplicitSyntax where
  mutual
    infix 3 _⁏_⊢_true
    data _⁏_⊢_true (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      var    : ∀ {A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊢ A true
      lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B true → Δ ⁏ Γ ⊢ A ⊃ B true
      app    : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B true → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ B true
      box    : ∀ {A} → Δ ⊢ A valid → Δ ⁏ Γ ⊢ □ A true
      use    : ∀ {A} → Δ ⊢ A valid → Δ ⁏ Γ ⊢ A true
      letbox : ∀ {A C} → Δ ⁏ Γ ⊢ □ A true → Δ , A valid ⁏ Γ ⊢ C true → Δ ⁏ Γ ⊢ C true
      pdia   : ∀ {A} → Δ ⁏ Γ ⊢ A poss → Δ ⁏ Γ ⊢ ◇ A true

    infix 3 _⊢_valid
    data _⊢_valid (Δ : ValidCtx) : Type → Set where
      vvar : ∀ {A} (x : Δ ∋ A valid) → Δ ⊢ A valid
      retv : ∀ {A} → Δ ⁏ · ⊢ A true → Δ ⊢ A valid

    infix 3 _⁏_⊢_poss
    data _⁏_⊢_poss (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      retp    : ∀ {A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ A poss
      letboxp : ∀ {A C} → Δ ⁏ Γ ⊢ □ A true → Δ , A valid ⁏ Γ ⊢ C poss → Δ ⁏ Γ ⊢ C poss
      letdiap : ∀ {A C} → Δ ⁏ Γ ⊢ ◇ A true → Δ ⁏ · , A true ⊢ C poss → Δ ⁏ Γ ⊢ C poss

------------------------------------------------------------------------------

-- NOTE: This semantics is mostly taken from Wijesekerae by way of Alechina et al.
-- https://github.com/dpndnt/library/blob/master/doc/pdf/alechina-et-al-2001.pdf
-- However, ≤→R is my own simplified frame condition, dubbed “vindication”, and it is
-- derivable from either “persistence” or “brilliance”.  Ono includes “persistence”,
-- but Alechina et al. only include “minor brilliance”.
--
-- _⨾_ : (World → World → Set) → (World → World → Set) → (World → World → Set)
-- (_R_ ⨾ _Q_) w w′ = Σ World (λ w″ → w R w″ × w″ Q w′)
--
-- _≤⨾R_ : World → World → Set
-- _≤⨾R_ = _≤_ ⨾ _R_
--
-- _R⨾≤_ : World → World → Set
-- _R⨾≤_ = _R_ ⨾ _≤_
--
-- field
--   persistence       : ∀ {w w′} → w ≤⨾R w′ → w R w′
--   brilliance        : ∀ {w w′} → w R⨾≤ w′ → w R w′
--   minor-persistence : ∀ {w w′} → w ≤⨾R w′ → w R⨾≤ w′
--   minor-brilliance  : ∀ {w w′} → w R⨾≤ w′ → w ≤⨾R w′

module _ {{M : Model}} where
  mutual
    infix 3 _⊩_true
    _⊩_true : World → Type → Set
    w ⊩ α P true   = w ⊩ P atomTrue
    w ⊩ A ⊃ B true = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A true → w′ ⊩ B true
    w ⊩ □ A true   = w ⊩ A valid
    w ⊩ ◇ A true   = w ⊩ A poss

    infix 3 _⊩_valid
    _⊩_valid : World → Type → Set
    w ⊩ A valid = ∀ {w′ : World} → w ≤ w′ → ∀ {w″} → w′ R w″ → w″ ⊩ A true

    infix 3 _⊩_poss
    _⊩_poss : World → Type → Set
    w ⊩ A poss = ∀ {w′ : World} → w ≤ w′ → Σ World λ w″ → w′ R w″ × w″ ⊩ A true

  infix 3 _⊩*_true
  _⊩*_true : World → List TrueAss → Set
  w ⊩* · true            = 𝟙
  w ⊩* (Γ , A true) true = w ⊩* Γ true × w ⊩ A true -- TODO: Ugly

  infix 3 _⊩*_valid
  _⊩*_valid : World → List ValidAss → Set
  w ⊩* · valid             = 𝟙
  w ⊩* (Δ , A valid) valid = w ⊩* Δ valid × w ⊩ A valid -- TODO: Ugly

  mono≤-valid : ∀ {w w′ A} → w ≤ w′ → w ⊩ A valid → w′ ⊩ A valid
  mono≤-valid η a η′ = a (trans≤ η η′)

  mono≤-poss : ∀ {w w′ A} → w ≤ w′ → w ⊩ A poss → w′ ⊩ A poss
  mono≤-poss η a η′ = a (trans≤ η η′)

  mono≤-true : ∀ {w w′ A} → w ≤ w′ → w ⊩ A true → w′ ⊩ A true
  mono≤-true {A = α P}   η a      = mono≤-atomTrue η a
  mono≤-true {A = A ⊃ B} η f η′ a = f (trans≤ η η′) a
  mono≤-true {A = □ A}   η a      = mono≤-valid {A = A} η a
  mono≤-true {A = ◇ A}   η a      = mono≤-poss {A = A} η a

  mono≤-true* : ∀ {w w′ Γ} → w ≤ w′ → w ⊩* Γ true → w′ ⊩* Γ true
  mono≤-true* {Γ = ·}          η ·       = ·
  mono≤-true* {Γ = Γ , A true} η (γ , a) = mono≤-true* η γ , mono≤-true {A = A} η a

  mono≤-valid* : ∀ {w w′ Δ} → w ≤ w′ → w ⊩* Δ valid → w′ ⊩* Δ valid
  mono≤-valid* {Δ = ·}           η ·       = ·
  mono≤-valid* {Δ = Δ , A valid} η (δ , a) = mono≤-valid* η δ , mono≤-valid {A = A} η a

  monoR-valid : ∀ {w w′ A} → w R w′ → w ⊩ A valid → w′ ⊩ A valid
  monoR-valid ζ a η ζ′ = a refl≤ (transR ζ (transR (≤→R η) ζ′))

  monoR-valid* : ∀ {w w′ Δ} → w R w′ → w ⊩* Δ valid → w′ ⊩* Δ valid
  monoR-valid* {Δ = ·}           ζ ·       = ·
  monoR-valid* {Δ = Δ , A valid} ζ (δ , a) = monoR-valid* ζ δ , monoR-valid {A = A} ζ a

------------------------------------------------------------------------------

infix 3 _⁏_⊨_true
_⁏_⊨_true : ValidCtx → TrueCtx → Type → Set₁
Δ ⁏ Γ ⊨ A true = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩* Γ true → w ⊩ A true

infix 3 _⊨_valid
_⊨_valid : ValidCtx → Type → Set₁
Δ ⊨ A valid = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩ A valid

infix 3 _⁏_⊨_poss
_⁏_⊨_poss : ValidCtx → TrueCtx → Type → Set₁
Δ ⁏ Γ ⊨ A poss = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩* Γ true → w ⊩ A poss

true⇒valid : ∀ {Δ A} → Δ ⁏ · ⊨ A true → Δ ⊨ A valid
true⇒valid a δ η ζ = a (monoR-valid* (transR (≤→R η) ζ) δ) ·

valid⇒true : ∀ {Δ Γ A} → Δ ⊨ A valid → Δ ⁏ Γ ⊨ A true
valid⇒true a δ γ = a δ refl≤ reflR

true⇒poss : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨ A poss
true⇒poss a δ γ η = _ , reflR , a (mono≤-valid* η δ) (mono≤-true* η γ)

cut-poss : ∀ {Δ Γ A C} → Δ ⁏ Γ ⊨ A poss → Δ ⁏ · , A true ⊨ C poss → Δ ⁏ Γ ⊨ C poss
cut-poss a c δ γ η = let _ , ζ  , a′ = a δ γ η in
                     let _ , ζ′ , c′ = c (monoR-valid* (transR (≤→R η) ζ) δ) (· , a′) refl≤ in
                     _ , transR ζ ζ′ , c′

⟦var⟧ : ∀ {Δ Γ A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊨ A true
⟦var⟧ top     δ (γ , a) = a
⟦var⟧ (pop x) δ (γ , a) = ⟦var⟧ x δ γ

⟦lam⟧ : ∀ {Δ Γ A B} → Δ ⁏ Γ , A true ⊨ B true → Δ ⁏ Γ ⊨ A ⊃ B true
⟦lam⟧ f δ γ η a = f (mono≤-valid* η δ) (mono≤-true* η γ , a)

⟦app⟧ : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊨ A ⊃ B true → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨ B true
⟦app⟧ f a δ γ = f δ γ refl≤ (a δ γ)

⟦box⟧ : ∀ {Δ Γ A} → Δ ⊨ A valid → Δ ⁏ Γ ⊨ □ A true
⟦box⟧ a δ γ = a δ

⟦use⟧ : ∀ {Δ Γ A} → Δ ⊨ A valid → Δ ⁏ Γ ⊨ A true
⟦use⟧ {A = A} a = valid⇒true {A = A} a

⟦letbox⟧ : ∀ {Δ Γ A C} → Δ ⁏ Γ ⊨ □ A true → Δ , A valid ⁏ Γ ⊨ C true → Δ ⁏ Γ ⊨ C true
⟦letbox⟧ a c δ γ = c (δ , a δ γ) γ

⟦pdia⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A poss → Δ ⁏ Γ ⊨ ◇ A true
⟦pdia⟧ a δ γ = a δ γ

⟦vvar⟧ : ∀ {Δ A} (x : Δ ∋ A valid) → Δ ⊨ A valid
⟦vvar⟧ top     (δ , a) = a
⟦vvar⟧ (pop x) (δ , a) = ⟦vvar⟧ x δ

⟦retv⟧ : ∀ {Δ A} → Δ ⁏ · ⊨ A true → Δ ⊨ A valid
⟦retv⟧ {A = A} a = true⇒valid {A = A} a

⟦retp⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨ A poss
⟦retp⟧ {A = A} a = true⇒poss {A = A} a

⟦letboxp⟧ : ∀ {Δ Γ A C} → Δ ⁏ Γ ⊨ □ A true → Δ , A valid ⁏ Γ ⊨ C poss → Δ ⁏ Γ ⊨ C poss
⟦letboxp⟧ a c δ γ = c (δ , a δ γ) γ

⟦letdiap⟧ : ∀ {Δ Γ A C} → Δ ⁏ Γ ⊨ ◇ A true → Δ ⁏ · , A true ⊨ C poss → Δ ⁏ Γ ⊨ C poss
⟦letdiap⟧ {A = A} {C} a c = cut-poss {A = A} {C} a c

⟦vvar⟧′ : ∀ {Δ Γ A} (x : Δ ∋ A valid) → Δ ⁏ Γ ⊨ A true
⟦vvar⟧′ {A = A} x = ⟦use⟧ {A = A} (⟦vvar⟧ x)

⟦box⟧′ : ∀ {Δ Γ A} → Δ ⁏ · ⊨ A true → Δ ⁏ Γ ⊨ □ A true
⟦box⟧′ {A = A} a = ⟦box⟧ {A = A} (⟦retv⟧ {A = A} a)

------------------------------------------------------------------------------

module ExplicitSemantics where
  open ExplicitSyntax

  mutual
    reflectTrue : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊨ A true
    reflectTrue (var x)                    = ⟦var⟧ x
    reflectTrue (lam {A = A} {B} t)        = ⟦lam⟧ {A = A} {B} (reflectTrue t)
    reflectTrue (app {A = A} {B} t₁ t₂)    = ⟦app⟧ {A = A} {B} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (box {A = A} t)            = ⟦box⟧ {A = A} (reflectValid t)
    reflectTrue (use {A = A} t)            = ⟦use⟧ {A = A} (reflectValid t)
    reflectTrue (letbox {A = A} {C} t₁ t₂) = ⟦letbox⟧ {A = A} {C} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (pdia {A = A} t)           = ⟦pdia⟧ {A = A} (reflectPoss t)

    reflectValid : ∀ {Δ A} → Δ ⊢ A valid → Δ ⊨ A valid
    reflectValid (vvar x)         = ⟦vvar⟧ x
    reflectValid (retv {A = A} t) = ⟦retv⟧ {A = A} (reflectTrue t)

    reflectPoss : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A poss → Δ ⁏ Γ ⊨ A poss
    reflectPoss (retp {A = A} t)            = ⟦retp⟧ {A = A} (reflectTrue t)
    reflectPoss (letboxp {A = A} {C} t₁ t₂) = ⟦letboxp⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)
    reflectPoss (letdiap {A = A} {C} t₁ t₂) = ⟦letdiap⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)

module ImplicitSemantics where
  open ImplicitSyntax

  mutual
    reflectTrue : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊨ A true
    reflectTrue (var x)                    = ⟦var⟧ x
    reflectTrue (lam {A = A} {B} t)        = ⟦lam⟧ {A = A} {B} (reflectTrue t)
    reflectTrue (app {A = A} {B} t₁ t₂)    = ⟦app⟧ {A = A} {B} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (vvar x)                   = ⟦vvar⟧′ x
    reflectTrue (box {A = A} t)            = ⟦box⟧′ {A = A} (reflectTrue t)
    reflectTrue (letbox {A = A} {C} t₁ t₂) = ⟦letbox⟧ {A = A} {C} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (pdia {A = A} t)           = ⟦pdia⟧ {A = A} (reflectPoss t)

    reflectPoss : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A poss → Δ ⁏ Γ ⊨ A poss
    reflectPoss (retp {A = A} t)            = ⟦retp⟧ {A = A} (reflectTrue t)
    reflectPoss (letboxp {A = A} {C} t₁ t₂) = ⟦letboxp⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)
    reflectPoss (letdiap {A = A} {C} t₁ t₂) = ⟦letdiap⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)

------------------------------------------------------------------------------

-- NOTE: This bidirectional syntax should probably be improved by separating
-- positive and negative types, following Abel-Sattler.
-- https://arxiv.org/pdf/1902.06097.pdf

-- mutual
--   infix 3 _⁏_⊢_checkTrue
--   data _⁏_⊢_checkTrue (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
--     lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B checkTrue → Δ ⁏ Γ ⊢ A ⊃ B checkTrue
--     box    : ∀ {A} → Δ ⊢ A checkValid → Δ ⁏ Γ ⊢ □ A checkTrue
--     letbox : ∀ {A C} → Δ ⁏ Γ ⊢ □ A synthTrue → Δ , A valid ⁏ Γ ⊢ C checkTrue → Δ ⁏ Γ ⊢ C checkTrue
--     dia    : ∀ {A} → Δ ⁏ Γ ⊢ A checkPoss → Δ ⁏ Γ ⊢ ◇ A checkTrue
--     check  : ∀ {P} → Δ ⁏ Γ ⊢ α P synthTrue → Δ ⁏ Γ ⊢ α P checkTrue

--   infix 3 _⁏_⊢_synthTrue
--   data _⁏_⊢_synthTrue (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
--     var : ∀ {A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊢ A synthTrue
--     app : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B synthTrue → Δ ⁏ Γ ⊢ A checkTrue → Δ ⁏ Γ ⊢ B synthTrue
--     use : ∀ {A} → Δ ⊢ A synthValid → Δ ⁏ Γ ⊢ A synthTrue

--   infix 3 _⊢_checkValid
--   data _⊢_checkValid (Δ : ValidCtx) : Type → Set where
--     retv   : ∀ {A} → Δ ⁏ · ⊢ A checkTrue → Δ ⊢ A checkValid
--     checkv : ∀ {P} → Δ ⊢ α P synthValid → Δ ⊢ α P checkValid

--   infix 3 _⊢_synthValid
--   data _⊢_synthValid (Δ : ValidCtx) : Type → Set where
--     vvar : ∀ {A} (x : Δ ∋ A valid) → Δ ⊢ A synthValid
--     retv : ∀ {A} → Δ ⁏ · ⊢ A synthTrue → Δ ⊢ A synthValid

--   infix 3 _⁏_⊢_checkPoss
--   data _⁏_⊢_checkPoss (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
--     retp    : ∀ {A} → Δ ⁏ Γ ⊢ A checkTrue → Δ ⁏ Γ ⊢ A checkPoss
--     letboxp : ∀ {A C} → Δ ⁏ Γ ⊢ □ A synthTrue → Δ , A valid ⁏ Γ ⊢ C checkPoss → Δ ⁏ Γ ⊢ C checkPoss
--     letdiap : ∀ {A C} → Δ ⁏ Γ ⊢ ◇ A synthTrue → Δ ⁏ · , A true ⊢ C checkPoss → Δ ⁏ Γ ⊢ C checkPoss
--     checkp  : ∀ {P} → Δ ⁏ Γ ⊢ α P synthPoss → Δ ⁏ Γ ⊢ α P checkPoss

--   infix 3 _⁏_⊢_synthPoss
--   data _⁏_⊢_synthPoss (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
--     retp : ∀ {A} → Δ ⁏ Γ ⊢ A synthTrue → Δ ⁏ Γ ⊢ A synthPoss

-- mutual
--   embCheckTrue : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A checkTrue → Δ ⁏ Γ ⊢ A true
--   embCheckTrue (lam t)        = lam (embCheckTrue t)
--   embCheckTrue (box t)        = box (embCheckValid t)
--   embCheckTrue (letbox t₁ t₂) = letbox (embSynthTrue t₁) (embCheckTrue t₂)
--   embCheckTrue (dia t)        = dia (embCheckPoss t)
--   embCheckTrue (check t)      = embSynthTrue t

--   embSynthTrue : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A synthTrue → Δ ⁏ Γ ⊢ A true
--   embSynthTrue (var x)     = var x
--   embSynthTrue (app t₁ t₂) = app (embSynthTrue t₁) (embCheckTrue t₂)
--   embSynthTrue (use t)     = use (embSynthValid t)

--   embCheckValid : ∀ {Δ A} → Δ ⊢ A checkValid → Δ ⊢ A valid
--   embCheckValid (retv t)   = retv (embCheckTrue t)
--   embCheckValid (checkv t) = embSynthValid t

--   embSynthValid : ∀ {Δ A} → Δ ⊢ A synthValid → Δ ⊢ A valid
--   embSynthValid (vvar x) = vvar x
--   embSynthValid (retv t) = retv (embSynthTrue t)

--   embCheckPoss : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A checkPoss → Δ ⁏ Γ ⊢ A poss
--   embCheckPoss (retp t)        = retp (embCheckTrue t)
--   embCheckPoss (letboxp t₁ t₂) = letboxp (embSynthTrue t₁) (embCheckPoss t₂)
--   embCheckPoss (letdiap t₁ t₂) = letdiap (embSynthTrue t₁) (embCheckPoss t₂)
--   embCheckPoss (checkp t)      = embSynthPoss t

--   embSynthPoss : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A synthPoss → Δ ⁏ Γ ⊢ A poss
--   embSynthPoss (retp t) = retp (embSynthTrue t)

-- ------------------------------------------------------------------------------

-- -- TODO: Boring
-- postulate
--   monoSynthTrue₁ : ∀ {Δ Δ′ Γ A} → Δ′ ⊒ Δ → Δ ⁏ Γ ⊢ A synthTrue → Δ′ ⁏ Γ ⊢ A synthTrue
--   monoSynthTrue₂ : ∀ {Δ Γ Γ′ A} → Γ′ ⊒ Γ → Δ ⁏ Γ ⊢ A synthTrue → Δ ⁏ Γ′ ⊢ A synthTrue

-- Ctx² : Set
-- Ctx² = ValidCtx × TrueCtx

-- _⊆²_ : Ctx² → Ctx² → Set
-- (Δ , Γ) ⊆² (Δ′ , Γ′) = Δ′ ⊒ Δ × Γ′ ⊒ Γ

-- refl⊆² : ∀ {Δ Γ} → (Δ , Γ) ⊆² (Δ , Γ)
-- refl⊆² = idr , idr

-- trans⊆² : ∀ {Δ Δ′ Δ″ Γ Γ′ Γ″} → (Δ , Γ) ⊆² (Δ′ , Γ′) → (Δ′ , Γ′) ⊆² (Δ″ , Γ″) → (Δ , Γ) ⊆² (Δ″ , Γ″)
-- trans⊆² (η₁ , η₂) (η₁′ , η₂′) = renr η₁′ η₁ , renr η₂′ η₂

-- wk₂⊆² : ∀ {Δ Δ′ Γ Γ′ C} → (Δ , Γ) ⊆² (Δ′ , Γ′) → (Δ , Γ) ⊆² (Δ′ , (Γ′ , C))
-- wk₂⊆² (η₁ , η₂) = η₁ , wkr η₂

-- _Я²_ : Ctx² → Ctx² → Set
-- (Δ , Γ) Я² (Δ′ , Γ′) = Δ′ ⊒ Δ

-- reflЯ² : ∀ {Δ Γ} → (Δ , Γ) Я² (Δ , Γ)
-- reflЯ² = idr

-- transЯ² : ∀ {Δ Δ′ Δ″ Γ Γ′ Γ″} → (Δ , Γ) Я² (Δ′ , Γ′) → (Δ′ , Γ′) Я² (Δ″ , Γ″) → (Δ , Γ) Я² (Δ″ , Γ″)
-- transЯ² η₁ η₁′ = renr η₁′ η₁

-- monoSynthTrue : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⊒ Δ × Γ′ ⊒ Γ → Δ ⁏ Γ ⊢ A synthTrue → Δ′ ⁏ Γ′ ⊢ A synthTrue
-- monoSynthTrue (η₁ , η₂) = monoSynthTrue₁ η₁ ∘ monoSynthTrue₂ η₂

-- instance
--   can : Model
--   can = record
--           { World         = ValidCtx × TrueCtx
--           ; _≤_           = _⊆²_
--           ; refl≤         = refl⊆²
--           ; trans≤        = trans⊆²
--           ; _R_           = _Я²_
--           ; reflR         = λ {w} → reflЯ² {Γ = π₂ w}
--           ; transR        = λ {w w′ w″} → transЯ² {Γ = π₂ w} {Γ′ = π₂ w′} {Γ″ = π₂ w″}
--           ; _⊩_atomTrue≤ = λ { (Δ , Γ) P → Δ ⁏ Γ ⊢ α P synthTrue }
--           ; mono≤-atomTrue≤ = monoSynthTrue
--           ; ≤→R          = π₁
--           }

-- -- NOTE: Instance resolution lets us now reuse each _⊩_ definitions by passing
-- -- a pair of context as a world.

-- mutual
--   reflectTrueCan : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A synthTrue → (Δ , Γ) ⊩ A true
--   reflectTrueCan {A = α P}   t = t
--   reflectTrueCan {A = A ⊃ B} t = λ η a → reflectTrueCan (app (monoSynthTrue η t) (reifyTrueCan a))
--   reflectTrueCan {A = □ A}   t = λ η ζ → {!!}
--   reflectTrueCan {A = ◇ A}   t = λ η → {!!}

--   reifyTrueCan : ∀ {Δ Γ A} → (Δ , Γ) ⊩ A true → Δ ⁏ Γ ⊢ A checkTrue
--   reifyTrueCan {A = α P}   t = check t
--   reifyTrueCan {A = A ⊃ B} f = lam (reifyTrueCan (f (wk₂⊆² refl⊆²) (reflectTrueCan {A = A} (var top))))
--   reifyTrueCan {A = □ A}   a = {!!}
--   reifyTrueCan {A = ◇ A}   a = {!!}

--   reflectValidCan : ∀ {Δ A} → Δ ⊢ A synthValid → (Δ , ·) ⊩ A valid
--   reflectValidCan {A = A} t = {!!}

--   reifyValidCan : ∀ {Δ A} → (Δ , ·) ⊩ A valid → Δ ⊢ A checkValid
--   reifyValidCan {A = A} a = {!!}

--   reflectPossCan : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A synthPoss → (Δ , Γ) ⊩ A poss
--   reflectPossCan {A = A} t = {!!}

--   reifyPossCan : ∀ {Δ Γ A} → (Δ , Γ) ⊩ A poss → Δ ⁏ Γ ⊢ A checkPoss
--   reifyPossCan {A = A} a = {!!}

-- ------------------------------------------------------------------------------
