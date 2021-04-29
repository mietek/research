module A202104.ICML where

open import A202103.Prelude public
open import A202103.List public
open import A202103.GenericRenaming public
open import A202104.Semantics public

------------------------------------------------------------------------------

mutual
  record TrueAss : Set where
    inductive
    constructor _true
    field
      A : Type

  TrueCtx = List TrueAss

  infixr 7 _⊃_
  data Type : Set where
    α_   : ∀ (P : Atom) → Type
    _⊃_  : ∀ (A B : Type) → Type
    [_]_ : ∀ (Ψ : TrueCtx) (A : Type) → Type
    ⟨_⟩_ : ∀ (Ψ : TrueCtx) (A : Type) → Type

record ValidAss : Set where
  constructor _valid[_]
  field
    A : Type
    Ψ : TrueCtx

ValidCtx = List ValidAss

module ImplicitSyntax where
  mutual
    infix 3 _⁏_⊢_true
    data _⁏_⊢_true (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      var    : ∀ {A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊢ A true
      lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B true → Δ ⁏ Γ ⊢ A ⊃ B true
      app    : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B true → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ B true
      vvar   : ∀ {Ψ A} (x : Δ ∋ A valid[ Ψ ]) → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊢ A true
      box    : ∀ {Ψ A} → Δ ⁏ Ψ ⊢ A true → Δ ⁏ Γ ⊢ [ Ψ ] A true
      letbox : ∀ {Ψ A C} → Δ ⁏ Γ ⊢ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊢ C true → Δ ⁏ Γ ⊢ C true
      dia    : ∀ {Ψ A} → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩ → Δ ⁏ Γ ⊢ ⟨ Ψ ⟩ A true

    infix 3 _⁏_⊢_poss⟨_⟩
    data _⁏_⊢_poss⟨_⟩ (Δ : ValidCtx) (Γ : TrueCtx) : Type → TrueCtx → Set where
      retp    : ∀ {Ψ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩
      letboxp : ∀ {Ψ Φ A C} → Δ ⁏ Γ ⊢ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊢ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊢ C poss⟨ Φ ⟩
      letdiap : ∀ {Ψ Φ A C} → Δ ⁏ Γ ⊢ ⟨ Ψ ⟩ A true → Δ ⁏ Ψ , A true ⊢ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊢ C poss⟨ Φ ⟩

    infix 3 _⁏_⊢*_
    _⁏_⊢*_ : ValidCtx → TrueCtx → TrueCtx → Set
    Δ ⁏ Γ ⊢* ·          = 𝟙
    Δ ⁏ Γ ⊢* Ψ , A true = Δ ⁏ Γ ⊢* Ψ × Δ ⁏ Γ ⊢ A true

module ExplicitSyntax where
  mutual
    infix 3 _⁏_⊢_true
    data _⁏_⊢_true (Δ : ValidCtx) (Γ : TrueCtx) : Type → Set where
      var    : ∀ {A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊢ A true
      lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B true → Δ ⁏ Γ ⊢ A ⊃ B true
      app    : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B true → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ B true
      box    : ∀ {Ψ A} → Δ ⊢ A valid[ Ψ ] → Δ ⁏ Γ ⊢ [ Ψ ] A true
      use    : ∀ {Ψ A} → Δ ⊢ A valid[ Ψ ] → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊢ A true
      letbox : ∀ {Ψ A C} → Δ ⁏ Γ ⊢ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊢ C true → Δ ⁏ Γ ⊢ C true
      dia    : ∀ {Ψ A} → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩ → Δ ⁏ Γ ⊢ ⟨ Ψ ⟩ A true

    infix 3 _⊢_valid[_]
    data _⊢_valid[_] (Δ : ValidCtx) : Type → TrueCtx → Set where
      vvar : ∀ {Ψ A} (x : Δ ∋ A valid[ Ψ ]) → Δ ⊢ A valid[ Ψ ]
      retv : ∀ {Ψ A} → Δ ⁏ Ψ ⊢ A true → Δ ⊢ A valid[ Ψ ]

    infix 3 _⁏_⊢_poss⟨_⟩
    data _⁏_⊢_poss⟨_⟩ (Δ : ValidCtx) (Γ : TrueCtx) : Type → TrueCtx → Set where
      retp    : ∀ {Ψ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩
      letboxp : ∀ {Ψ Φ A C} → Δ ⁏ Γ ⊢ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊢ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊢ C poss⟨ Φ ⟩
      letdiap : ∀ {Ψ Φ A C} → Δ ⁏ Γ ⊢ ⟨ Ψ ⟩ A true → Δ ⁏ Ψ , A true ⊢ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊢ C poss⟨ Φ ⟩

    infix 3 _⁏_⊢*_
    _⁏_⊢*_ : ValidCtx → TrueCtx → TrueCtx → Set
    Δ ⁏ Γ ⊢* ·          = 𝟙
    Δ ⁏ Γ ⊢* Ψ , A true = Δ ⁏ Γ ⊢* Ψ × Δ ⁏ Γ ⊢ A true

------------------------------------------------------------------------------

module _ {{M : Model}} where
  mutual
    infix 3 _⊩_true
    _⊩_true : World → Type → Set
    w ⊩ α P true     = w ⊩ P atomTrue
    w ⊩ A ⊃ B true   = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A true → w′ ⊩ B true
    w ⊩ [ Ψ ] A true = w ⊩ A valid[ Ψ ]
    w ⊩ ⟨ Ψ ⟩ A true = w ⊩ A poss⟨ Ψ ⟩

    infix 3 _⊩_valid[_]
    _⊩_valid[_] : World → Type → TrueCtx → Set
    w ⊩ A valid[ Ψ ] = ∀ {w′ : World} → w ≤ w′ → ∀ {w″} → w′ R w″ → w″ ⊩* Ψ true → w″ ⊩ A true

    infix 3 _⊩_poss⟨_⟩
    _⊩_poss⟨_⟩ : World → Type → TrueCtx → Set
    w ⊩ A poss⟨ Ψ ⟩ = ∀ {w′ : World} → w ≤ w′ → Σ World λ w″ → w′ R w″ × w″ ⊩* Ψ true × w″ ⊩ A true

    infix 3 _⊩*_true
    _⊩*_true : World → List TrueAss → Set
    w ⊩* · true            = 𝟙
    w ⊩* (Γ , A true) true = w ⊩* Γ true × w ⊩ A true -- TODO: Ugly

  infix 3 _⊩*_valid
  _⊩*_valid : World → List ValidAss → Set
  w ⊩* · valid                  = 𝟙
  w ⊩* (Δ , A valid[ Ψ ]) valid = w ⊩* Δ valid × w ⊩ A valid[ Ψ ] -- TODO: Ugly

  mono≤-valid : ∀ {w w′ Ψ A} → w ≤ w′ → w ⊩ A valid[ Ψ ] → w′ ⊩ A valid[ Ψ ]
  mono≤-valid η a η′ = a (trans≤ η η′)

  mono≤-poss : ∀ {w w′ Ψ A} → w ≤ w′ → w ⊩ A poss⟨ Ψ ⟩ → w′ ⊩ A poss⟨ Ψ ⟩
  mono≤-poss η a η′ = a (trans≤ η η′)

  mono≤-true : ∀ {w w′ A} → w ≤ w′ → w ⊩ A true → w′ ⊩ A true
  mono≤-true {A = α P}     η a      = mono≤-atomTrue η a
  mono≤-true {A = A ⊃ B}   η f η′ a = f (trans≤ η η′) a
  mono≤-true {A = [ Ψ ] A} η a      = mono≤-valid {A = A} η a
  mono≤-true {A = ⟨ Ψ ⟩ A} η a      = mono≤-poss {A = A} η a

  mono≤-true* : ∀ {w w′ Γ} → w ≤ w′ → w ⊩* Γ true → w′ ⊩* Γ true
  mono≤-true* {Γ = ·}          η ·       = ·
  mono≤-true* {Γ = Γ , A true} η (γ , a) = mono≤-true* η γ , mono≤-true {A = A} η a

  mono≤-valid* : ∀ {w w′ Δ} → w ≤ w′ → w ⊩* Δ valid → w′ ⊩* Δ valid
  mono≤-valid* {Δ = ·}                η ·       = ·
  mono≤-valid* {Δ = Δ , A valid[ Ψ ]} η (δ , a) = mono≤-valid* η δ , mono≤-valid {A = A} η a

  monoR-valid : ∀ {w w′ Ψ A} → w R w′ → w ⊩ A valid[ Ψ ] → w′ ⊩ A valid[ Ψ ]
  monoR-valid ζ a η ζ′ = a refl≤ (transR ζ (transR (≤→R η) ζ′))

  monoR-valid* : ∀ {w w′ Δ} → w R w′ → w ⊩* Δ valid → w′ ⊩* Δ valid
  monoR-valid* {Δ = ·}                ζ ·       = ·
  monoR-valid* {Δ = Δ , A valid[ Ψ ]} ζ (δ , a) = monoR-valid* ζ δ , monoR-valid {A = A} ζ a

------------------------------------------------------------------------------

infix 3 _⁏_⊨_true
_⁏_⊨_true : ValidCtx → TrueCtx → Type → Set₁
Δ ⁏ Γ ⊨ A true = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩* Γ true → w ⊩ A true

infix 3 _⊨_valid[_]
_⊨_valid[_] : ValidCtx → Type → TrueCtx → Set₁
Δ ⊨ A valid[ Ψ ] = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩ A valid[ Ψ ]

infix 3 _⁏_⊨_poss⟨_⟩
_⁏_⊨_poss⟨_⟩ : ValidCtx → TrueCtx → Type → TrueCtx → Set₁
Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩ = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩* Γ true → w ⊩ A poss⟨ Ψ ⟩

infix 3 _⁏_⊨*_true
_⁏_⊨*_true : ValidCtx → TrueCtx → List TrueAss → Set₁
Δ ⁏ Γ ⊨* Ψ true = ∀ {{M : Model}} {w : World} → w ⊩* Δ valid → w ⊩* Γ true → w ⊩* Ψ true

true⇒valid : ∀ {Δ Ψ A} → Δ ⁏ Ψ ⊨ A true → Δ ⊨ A valid[ Ψ ]
true⇒valid a δ η ζ ψ = a (monoR-valid* (transR (≤→R η) ζ) δ) ψ

valid⇒true : ∀ {Δ Γ Ψ A} → Δ ⊨ A valid[ Ψ ] → Δ ⁏ Γ ⊨* Ψ true → Δ ⁏ Γ ⊨ A true
valid⇒true a ψ δ γ = a δ refl≤ reflR (ψ δ γ)

true⇒poss : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨* Ψ true → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩
true⇒poss {A = A} a ψ δ γ η = _ , reflR , mono≤-true* η (ψ δ γ) , mono≤-true {A = A} η (a δ γ)

cut-poss : ∀ {Δ Γ Ψ Φ A C} → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩ → Δ ⁏ Ψ , A true ⊨ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊨ C poss⟨ Φ ⟩
cut-poss a c δ γ η = let _ , ζ  , ψ , a′ = a δ γ η in
                     let _ , ζ′ , c′ = c (monoR-valid* (transR (≤→R η) ζ) δ) (ψ , a′) refl≤ in
                     _ , transR ζ ζ′ , c′

⟦var⟧ : ∀ {Δ Γ A} (x : Γ ∋ A true) → Δ ⁏ Γ ⊨ A true
⟦var⟧ top     δ (γ , a) = a
⟦var⟧ (pop x) δ (γ , a) = ⟦var⟧ x δ γ

⟦lam⟧ : ∀ {Δ Γ A B} → Δ ⁏ Γ , A true ⊨ B true → Δ ⁏ Γ ⊨ A ⊃ B true
⟦lam⟧ f δ γ η a = f (mono≤-valid* η δ) (mono≤-true* η γ , a)

⟦app⟧ : ∀ {Δ Γ A B} → Δ ⁏ Γ ⊨ A ⊃ B true → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨ B true
⟦app⟧ f a δ γ = f δ γ refl≤ (a δ γ)

⟦box⟧ : ∀ {Δ Γ Ψ A} → Δ ⊨ A valid[ Ψ ] → Δ ⁏ Γ ⊨ [ Ψ ] A true
⟦box⟧ a δ γ = a δ

⟦use⟧ : ∀ {Δ Γ Ψ A} → Δ ⊨ A valid[ Ψ ] → Δ ⁏ Γ ⊨* Ψ true → Δ ⁏ Γ ⊨ A true
⟦use⟧ {A = A} a = valid⇒true {A = A} a

⟦letbox⟧ : ∀ {Δ Γ Ψ A C} → Δ ⁏ Γ ⊨ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊨ C true → Δ ⁏ Γ ⊨ C true
⟦letbox⟧ a c δ γ = c (δ , a δ γ) γ

⟦dia⟧ : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩ → Δ ⁏ Γ ⊨ ⟨ Ψ ⟩ A true
⟦dia⟧ a δ γ = a δ γ

⟦vvar⟧ : ∀ {Δ Ψ A} (x : Δ ∋ A valid[ Ψ ]) → Δ ⊨ A valid[ Ψ ]
⟦vvar⟧ top     (δ , a) = a
⟦vvar⟧ (pop x) (δ , a) = ⟦vvar⟧ x δ

⟦retv⟧ : ∀ {Δ Ψ A} → Δ ⁏ Ψ ⊨ A true → Δ ⊨ A valid[ Ψ ]
⟦retv⟧ {A = A} a = true⇒valid {A = A} a

⟦retp⟧ : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊨ A true → Δ ⁏ Γ ⊨* Ψ true → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩
⟦retp⟧ {A = A} a = true⇒poss {A = A} a

⟦letboxp⟧ : ∀ {Δ Γ Ψ Φ A C} → Δ ⁏ Γ ⊨ [ Ψ ] A true → Δ , A valid[ Ψ ] ⁏ Γ ⊨ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊨ C poss⟨ Φ ⟩
⟦letboxp⟧ a c δ γ = c (δ , a δ γ) γ

⟦letdiap⟧ : ∀ {Δ Γ Ψ Φ A C} → Δ ⁏ Γ ⊨ ⟨ Ψ ⟩ A true → Δ ⁏ Ψ , A true ⊨ C poss⟨ Φ ⟩ → Δ ⁏ Γ ⊨ C poss⟨ Φ ⟩
⟦letdiap⟧ {A = A} {C} a c = cut-poss {A = A} {C} a c

⟦vvar⟧′ : ∀ {Δ Γ Ψ A} (x : Δ ∋ A valid[ Ψ ]) → Δ ⁏ Γ ⊨* Ψ true → Δ ⁏ Γ ⊨ A true
⟦vvar⟧′ {A = A} x ψ = ⟦use⟧ {A = A} (⟦vvar⟧ x) ψ

⟦box⟧′ : ∀ {Δ Γ Ψ A} → Δ ⁏ Ψ ⊨ A true → Δ ⁏ Γ ⊨ [ Ψ ] A true
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
    reflectTrue (use {A = A} t σ)          = ⟦use⟧ {A = A} (reflectValid t) (reflect* σ)
    reflectTrue (letbox {A = A} {C} t₁ t₂) = ⟦letbox⟧ {A = A} {C} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (dia {A = A} t)            = ⟦dia⟧ {A = A} (reflectPoss t)

    reflectValid : ∀ {Δ Ψ A} → Δ ⊢ A valid[ Ψ ] → Δ ⊨ A valid[ Ψ ]
    reflectValid (vvar x)         = ⟦vvar⟧ x
    reflectValid (retv {A = A} t) = ⟦retv⟧ {A = A} (reflectTrue t)

    reflectPoss : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩ → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩
    reflectPoss (retp {A = A} t σ)          = ⟦retp⟧ {A = A} (reflectTrue t) (reflect* σ)
    reflectPoss (letboxp {A = A} {C} t₁ t₂) = ⟦letboxp⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)
    reflectPoss (letdiap {A = A} {C} t₁ t₂) = ⟦letdiap⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)

    reflect* : ∀ {Δ Γ Ψ} → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊨* Ψ true
    reflect* {Ψ = ·}          ·       = λ δ γ → ·
    reflect* {Ψ = Ψ , A true} (σ , t) = λ δ γ → reflect* σ δ γ , reflectTrue t δ γ

module ImplicitSemantics where
  open ImplicitSyntax

  mutual
    reflectTrue : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊨ A true
    reflectTrue (var x)                    = ⟦var⟧ x
    reflectTrue (lam {A = A} {B} t)        = ⟦lam⟧ {A = A} {B} (reflectTrue t)
    reflectTrue (app {A = A} {B} t₁ t₂)    = ⟦app⟧ {A = A} {B} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (vvar x σ)                 = ⟦vvar⟧′ x (reflect* σ)
    reflectTrue (box {A = A} t)            = ⟦box⟧′ {A = A} (reflectTrue t)
    reflectTrue (letbox {A = A} {C} t₁ t₂) = ⟦letbox⟧ {A = A} {C} (reflectTrue t₁) (reflectTrue t₂)
    reflectTrue (dia {A = A} t)            = ⟦dia⟧ {A = A} (reflectPoss t)

    reflectPoss : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊢ A poss⟨ Ψ ⟩ → Δ ⁏ Γ ⊨ A poss⟨ Ψ ⟩
    reflectPoss (retp {A = A} t σ)          = ⟦retp⟧ {A = A} (reflectTrue t) (reflect* σ)
    reflectPoss (letboxp {A = A} {C} t₁ t₂) = ⟦letboxp⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)
    reflectPoss (letdiap {A = A} {C} t₁ t₂) = ⟦letdiap⟧ {A = A} {C} (reflectTrue t₁) (reflectPoss t₂)

    reflect* : ∀ {Δ Γ Ψ} → Δ ⁏ Γ ⊢* Ψ → Δ ⁏ Γ ⊨* Ψ true
    reflect* {Ψ = ·}          ·       = λ δ γ → ·
    reflect* {Ψ = Ψ , A true} (σ , t) = λ δ γ → reflect* σ δ γ , reflectTrue t δ γ

------------------------------------------------------------------------------
