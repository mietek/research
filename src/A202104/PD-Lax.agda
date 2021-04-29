module A202104.PD-Lax where

open import A202103.Prelude public
open import A202103.List public
open import A202103.GenericRenaming public
open import A202104.Semantics public

module M where
  import A202104.PD
  open A202104.PD public hiding (module ImplicitSyntax ; module ExplicitSyntax)
  open A202104.PD.ImplicitSyntax public

open M using () renaming (_⁏_⊢_true to _⁏_⊢ᴹ_true ; _⁏_⊢_poss to _⁏_⊢ᴹ_poss)

------------------------------------------------------------------------------

module ToM where
  open M

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

------------------------------------------------------------------------------

infixr 7 _⇒_
data Type : Set where
  α_   : ∀ (P : Atom) → Type
  _⇒_ : ∀ (A B : Type) → Type
  ○_   : ∀ (A : Type) → Type

record TrueAss : Set where
  constructor _true
  field
    A : Type

TrueCtx = List TrueAss

mutual
  infix 3 _⊢_true
  data _⊢_true (Γ : TrueCtx) : Type → Set where
    var : ∀ {A} (x : Γ ∋ A true) → Γ ⊢ A true
    lam : ∀ {A B} → Γ , A true ⊢ B true → Γ ⊢ A ⇒ B true
    app : ∀ {A B} → Γ ⊢ A ⇒ B true → Γ ⊢ A true → Γ ⊢ B true
    cir : ∀ {A} → Γ ⊢ A lax → Γ ⊢ ○ A true

  infix 3 _⊢_lax
  data _⊢_lax (Γ : TrueCtx) : Type → Set where
    ret    : ∀ {A} → Γ ⊢ A true → Γ ⊢ A lax
    letcir : ∀ {A C} → Γ ⊢ ○ A true → Γ , A true ⊢ C lax → Γ ⊢ C lax

law₁ : ∀ {Γ A} → Γ ⊢ A ⇒ ○ A true
law₁ = lam (cir (ret (var top)))

law₂ : ∀ {Γ A} → Γ ⊢ ○ ○ A ⇒ ○ A true
law₂ = lam (cir (letcir (var top) (letcir (var top) (ret (var top)))))

law₃ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) ⇒ (○ A ⇒ ○ B) true
law₃ = lam (lam (cir (letcir (var top) (ret (app (var (pop (pop top))) (var top))))))

⟦_⟧+ : Type → M.Type
⟦ α P ⟧+    = M.α P
⟦ A ⇒ B ⟧+ = M.□ ⟦ A ⟧+ M.⊃ ⟦ B ⟧+
⟦ ○ A ⟧+    = M.◇ M.□ ⟦ A ⟧+

⟦_⟧++ : TrueCtx → M.ValidCtx
⟦ · ⟧++          = ·
⟦ Γ , A true ⟧++ = ⟦ Γ ⟧++ , ⟦ A ⟧+ M.valid

to-vass : ∀ {Γ A} → Γ ∋ A true → ⟦ Γ ⟧++ ∋ ⟦ A ⟧+ M.valid
to-vass top     = top
to-vass (pop x) = pop (to-vass x)

mutual
  to-true : ∀ {Γ A} → Γ ⊢ A true → ⟦ Γ ⟧++ ⁏ · ⊢ᴹ ⟦ A ⟧+ true
  to-true (var x)     = M.vvar (to-vass x)
  to-true (lam t)     = ToM.llam (to-true t)
  to-true (app t₁ t₂) = ToM.lapp (to-true t₁) (to-true t₂)
  to-true (cir t)     = ToM.cir (to-poss t)

  to-poss : ∀ {Γ A} → Γ ⊢ A lax → ⟦ Γ ⟧++ ⁏ · ⊢ᴹ M.□ ⟦ A ⟧+ poss
  to-poss (ret t)        = M.retp (M.box (to-true t))
  to-poss (letcir t₁ t₂) = ToM.letcir (to-true t₁) (to-poss t₂)

⟦_⟧- : M.Type → Type
⟦ M.α P ⟧-   = α P
⟦ A M.⊃ B ⟧- = ⟦ A ⟧- ⇒ ⟦ B ⟧-
⟦ M.□ A ⟧-   = ⟦ A ⟧-
⟦ M.◇ A ⟧-   = ○ ⟦ A ⟧-

-- TODO: Finish the other direction

------------------------------------------------------------------------------

-- NOTE: This semantics is based on the Pfenning-Davies syntactic translation above.
-- It would be nice to define a semantics directly.

module IndirectSemantics where
  module _ {{M : Model}} where
    infix 3 _⊩_true
    _⊩_true : World → Type → Set
    w ⊩ A true = w M.⊩ ⟦ A ⟧+ true

    infix 3 _⊩_lax
    _⊩_lax : World → Type → Set
    w ⊩ A lax = w M.⊩ M.□ ⟦ A ⟧+ poss

    infix 3 _⊩*_true
    _⊩*_true : World → List TrueAss → Set
    w ⊩* Γ true = w M.⊩* ⟦ Γ ⟧++ valid

    mono≤-true : ∀ {w w′ A} → w ≤ w′ → w ⊩ A true → w′ ⊩ A true
    mono≤-true {A = A} η a = M.mono≤-true {A = ⟦ A ⟧+} η a

    mono≤-lax : ∀ {w w′ A} → w ≤ w′ → w ⊩ A lax → w′ ⊩ A lax
    mono≤-lax {A = A} η a = M.mono≤-poss {A = M.□ ⟦ A ⟧+} η a

    mono≤-true* : ∀ {w w′ Γ} → w ≤ w′ → w ⊩* Γ true → w′ ⊩* Γ true
    mono≤-true* η γ = M.mono≤-valid* η γ

    monoR-true* : ∀ {w w′ Γ} → w R w′ → w ⊩* Γ true → w′ ⊩* Γ true
    monoR-true* ζ γ = M.monoR-valid* ζ γ

  infix 3 _⊨_true
  _⊨_true : TrueCtx → Type → Set₁
  Γ ⊨ A true = ∀ {{M : Model}} {w : World} → w ⊩* Γ true → w ⊩ A true

  infix 3 _⊨_lax
  _⊨_lax : TrueCtx → Type → Set₁
  Γ ⊨ A lax = ∀ {{M : Model}} {w : World} → w ⊩* Γ true → w ⊩ A lax

  true⇒lax : ∀ {Γ A} → Γ ⊨ A true → Γ ⊨ A lax
  true⇒lax a γ η = _ , reflR , λ η′ ζ → a (monoR-true* (transR (≤→R (trans≤ η η′)) ζ) γ)

  cut-lax : ∀ {Γ A C} → Γ ⊨ A lax → Γ , A true ⊨ C lax → Γ ⊨ C lax
  cut-lax a c γ η = let _ , ζ  , a′ = a γ η in
                    let _ , ζ′ , c′ = c (monoR-true* (transR (≤→R η) ζ) γ , a′) refl≤ in
                    _ , transR ζ ζ′ , c′

  ⟦var⟧ : ∀ {Γ A} (x : Γ ∋ A true) → Γ ⊨ A true
  ⟦var⟧ top     (γ , a) = a refl≤ reflR
  ⟦var⟧ (pop x) (γ , a) = ⟦var⟧ x γ

  ⟦lam⟧ : ∀ {Γ A B} → Γ , A true ⊨ B true → Γ ⊨ A ⇒ B true
  ⟦lam⟧ f γ η a = f (mono≤-true* η γ , a)

  ⟦app⟧ : ∀ {Γ A B} → Γ ⊨ A ⇒ B true → Γ ⊨ A true → Γ ⊨ B true
  ⟦app⟧ f a γ = f γ refl≤ λ η′ ζ → a (monoR-true* (transR (≤→R η′) ζ) γ)

  ⟦cir⟧ : ∀ {Γ A} → Γ ⊨ A lax → Γ ⊨ ○ A true
  ⟦cir⟧ a γ η = a γ η

  ⟦ret⟧ : ∀ {Γ A} → Γ ⊨ A true → Γ ⊨ A lax
  ⟦ret⟧ {A = A} a = true⇒lax {A = A} a

  ⟦letcir⟧ : ∀ {Γ A C} → Γ ⊨ ○ A true → Γ , A true ⊨ C lax → Γ ⊨ C lax
  ⟦letcir⟧ {A = A} {C} a c = cut-lax {A = A} {C} a c

  mutual
    reflectTrue : ∀ {Γ A} → Γ ⊢ A true → Γ ⊨ A true
    reflectTrue (var x)                 = ⟦var⟧ x
    reflectTrue (lam {A = A} {B} t)     = ⟦lam⟧ {A = A} {B} (reflectTrue t)
    reflectTrue (app {A = A} {B} t₁ t₂) = ⟦app⟧ {A = A} {B} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (cir {A = A} t)         = ⟦cir⟧ {A = A} (reflectLax t)

    reflectLax : ∀ {Γ A} → Γ ⊢ A lax → Γ ⊨ A lax
    reflectLax (ret {A = A} t)            = ⟦ret⟧ {A = A} (reflectTrue t)
    reflectLax (letcir {A = A} {C} t₁ t₂) = ⟦letcir⟧ {A = A} {C} (reflectTrue t₁) (reflectLax t₂)

------------------------------------------------------------------------------

module DirectSemantics where
  module _ {{M : Model}} where
    mutual
      infix 3 _⊩_true
      _⊩_true : World → Type → Set
      w ⊩ α P true    = w ⊩ P atomTrue
      w ⊩ A ⇒ B true = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A valid → w′ ⊩ B true
      w ⊩ ○ A true    = w ⊩ A lax

      infix 3 _⊩_lax
      _⊩_lax : World → Type → Set
      w ⊩ A lax = ∀ {w′ : World} → w ≤ w′ → Σ World λ w″ → w′ R w″ × w″ ⊩ A valid

      infix 3 _⊩_valid
      _⊩_valid : World → Type → Set
      w ⊩ A valid = ∀ {w′ : World} → w ≤ w′ → ∀ {w″} → w′ R w″ → w″ ⊩ A true

    infix 3 _⊩*_valid
    _⊩*_valid : World → List TrueAss → Set
    w ⊩* · valid            = 𝟙
    w ⊩* (Γ , A true) valid = w ⊩* Γ valid × w ⊩ A valid -- TODO: Ugly

    mono≤-lax : ∀ {w w′ A} → w ≤ w′ → w ⊩ A lax → w′ ⊩ A lax
    mono≤-lax η a η′ = a (trans≤ η η′)

    mono≤-true : ∀ {w w′ A} → w ≤ w′ → w ⊩ A true → w′ ⊩ A true
    mono≤-true {A = α P}    η a      = mono≤-atomTrue η a
    mono≤-true {A = A ⇒ B} η f η′ a = f (trans≤ η η′) a
    mono≤-true {A = ○ A}    η a      = mono≤-lax {A = A} η a

    mono≤-valid : ∀ {w w′ A} → w ≤ w′ → w ⊩ A valid → w′ ⊩ A valid
    mono≤-valid {A = A} η a η′ = a (trans≤ η η′)

    mono≤-valid* : ∀ {w w′ Γ} → w ≤ w′ → w ⊩* Γ valid → w′ ⊩* Γ valid
    mono≤-valid* {Γ = ·}          η ·       = ·
    mono≤-valid* {Γ = Γ , A true} η (γ , a) = mono≤-valid* η γ , mono≤-valid {A = A} η a

    monoR-valid : ∀ {w w′ A} → w R w′ → w ⊩ A valid → w′ ⊩ A valid
    monoR-valid {A = A} ζ a η ζ′ = a refl≤ (transR (transR ζ (≤→R η)) ζ′)

    monoR-valid* : ∀ {w w′ Γ} → w R w′ → w ⊩* Γ valid → w′ ⊩* Γ valid
    monoR-valid* {Γ = ·}          η ·       = ·
    monoR-valid* {Γ = Γ , A true} η (γ , a) = monoR-valid* η γ , monoR-valid {A = A} η a

  infix 3 _⊨_true
  _⊨_true : TrueCtx → Type → Set₁
  Γ ⊨ A true = ∀ {{M : Model}} {w : World} → w ⊩* Γ valid → w ⊩ A true

  infix 3 _⊨_lax
  _⊨_lax : TrueCtx → Type → Set₁
  Γ ⊨ A lax = ∀ {{M : Model}} {w : World} → w ⊩* Γ valid → w ⊩ A lax

  true⇒lax : ∀ {Γ A} → Γ ⊨ A true → Γ ⊨ A lax
  true⇒lax a γ η = _ , reflR , λ η′ ζ → a (monoR-valid* (transR (≤→R (trans≤ η η′)) ζ) γ)

  cut-lax : ∀ {Γ A C} → Γ ⊨ A lax → Γ , A true ⊨ C lax → Γ ⊨ C lax
  cut-lax a c γ η = let _ , ζ  , a′ = a γ η in
                    let _ , ζ′ , c′ = c (monoR-valid* (transR (≤→R η) ζ) γ , a′) refl≤ in
                    _ , transR ζ ζ′ , c′

  ⟦var⟧ : ∀ {Γ A} (x : Γ ∋ A true) → Γ ⊨ A true
  ⟦var⟧ top     (γ , a) = a refl≤ reflR
  ⟦var⟧ (pop x) (γ , a) = ⟦var⟧ x γ

  ⟦lam⟧ : ∀ {Γ A B} → Γ , A true ⊨ B true → Γ ⊨ A ⇒ B true
  ⟦lam⟧ f γ η a = f (mono≤-valid* η γ , a)

  ⟦app⟧ : ∀ {Γ A B} → Γ ⊨ A ⇒ B true → Γ ⊨ A true → Γ ⊨ B true
  ⟦app⟧ f a γ = f γ refl≤ λ η′ ζ → a (monoR-valid* (transR (≤→R η′) ζ) γ)

  ⟦cir⟧ : ∀ {Γ A} → Γ ⊨ A lax → Γ ⊨ ○ A true
  ⟦cir⟧ a γ η = a γ η

  ⟦ret⟧ : ∀ {Γ A} → Γ ⊨ A true → Γ ⊨ A lax
  ⟦ret⟧ {A = A} a = true⇒lax {A = A} a

  ⟦letcir⟧ : ∀ {Γ A C} → Γ ⊨ ○ A true → Γ , A true ⊨ C lax → Γ ⊨ C lax
  ⟦letcir⟧ {A = A} {C} a c = cut-lax {A = A} {C} a c

  mutual
    reflectTrue : ∀ {Γ A} → Γ ⊢ A true → Γ ⊨ A true
    reflectTrue (var x)                 = ⟦var⟧ x
    reflectTrue (lam {A = A} {B} t)     = ⟦lam⟧ {A = A} {B} (reflectTrue t)
    reflectTrue (app {A = A} {B} t₁ t₂) = ⟦app⟧ {A = A} {B} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (cir {A = A} t)         = ⟦cir⟧ {A = A} (reflectLax t)

    reflectLax : ∀ {Γ A} → Γ ⊢ A lax → Γ ⊨ A lax
    reflectLax (ret {A = A} t)            = ⟦ret⟧ {A = A} (reflectTrue t)
    reflectLax (letcir {A = A} {C} t₁ t₂) = ⟦letcir⟧ {A = A} {C} (reflectTrue t₁) (reflectLax t₂)

------------------------------------------------------------------------------
