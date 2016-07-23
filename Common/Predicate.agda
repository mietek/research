module Common.Predicate where

open import Common public

open import Common.Context public
  using (Cx ; VCx ; ⌀ ; _,_)


-- Predicates.

Pred : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
Pred {ℓ} U = U → Set ℓ


-- Set membership.

module _ {U : Set} where
  infix 3 _∈ᴾ_
  _∈ᴾ_ : U → Pred U → Set
  A ∈ᴾ P = P A

  infix 3 _∉ᴾ_
  _∉ᴾ_ : U → Pred U → Set
  A ∉ᴾ P = Not (A ∈ᴾ P)


-- Empty set.

module _ {U : Set} where
  ⌀ᴾ : Pred U
  ⌀ᴾ = const Bot

  bot∈ᴾ : ∀ {A} → A ∉ᴾ ⌀ᴾ
  bot∈ᴾ = elimBot


-- Universal set.

module _ {U : Set} where
  Uᴾ : Pred U
  Uᴾ = const Top

  top∈ᴾ : ∀ {A} → A ∈ᴾ Uᴾ
  top∈ᴾ = ∙


-- Set inclusion.

module _ {U : Set} where
  infix 3 _⊆ᴾ_
  _⊆ᴾ_ : Pred U → Pred U → Set
  P ⊆ᴾ Q = ∀ {A : U} → A ∈ᴾ P → A ∈ᴾ Q

  infix 3 _⊈ᴾ_
  _⊈ᴾ_ : Pred U → Pred U → Set
  P ⊈ᴾ Q = Not (P ⊆ᴾ Q)

  refl⊆ᴾ : ∀ {P} → P ⊆ᴾ P
  refl⊆ᴾ = id

  trans⊆ᴾ : ∀ {P Q R} → P ⊆ᴾ Q → Q ⊆ᴾ R → P ⊆ᴾ R
  trans⊆ᴾ η η′ = η′ ∘ η

  bot⊆ᴾ : ∀ {P} → ⌀ᴾ ⊆ᴾ P
  bot⊆ᴾ = elimBot

  top⊆ᴾ : ∀ {P} → P ⊆ᴾ Uᴾ
  top⊆ᴾ = const ∙


-- Set equality.

module _ {U : Set} where
  infix 3 _⫗ᴾ_
  _⫗ᴾ_ : Pred U → Pred U → Set
  P ⫗ᴾ Q = (P ⊆ᴾ Q) × (Q ⊆ᴾ P)

  refl⫗ᴾ : ∀ {P} → P ⫗ᴾ P
  refl⫗ᴾ {P} = refl⊆ᴾ {P = P} , refl⊆ᴾ {P = P}

  trans⫗ᴾ : ∀ {P Q R} → P ⫗ᴾ Q → Q ⫗ᴾ R → P ⫗ᴾ R
  trans⫗ᴾ {P} (η , μ) (η′ , μ′) = trans⊆ᴾ {P = P} η η′ , trans⊆ᴾ {R = P} μ′ μ

  sym⫗ᴾ : ∀ {P Q} → P ⫗ᴾ Q → Q ⫗ᴾ P
  sym⫗ᴾ (η , μ) = (μ , η)

  antisym⊆ᴾ : ∀ {P Q} → ((P ⊆ᴾ Q) × (Q ⊆ᴾ P)) ≡ (P ⫗ᴾ Q)
  antisym⊆ᴾ = refl


-- Predicate-based necessity.

module _ {U : Set} where
  data All (P : Pred U) : Pred (Cx U) where
    ⌀   : All P ⌀
    _,_ : ∀ {A Γ} → All P Γ → P A → All P (Γ , A)

  fill : ∀ {Γ P} → (∀ A → P A) → All P Γ
  fill {⌀}     f = ⌀
  fill {Γ , A} f = fill f , f A

  mapAll : ∀ {P Q} → P ⊆ᴾ Q → All P ⊆ᴾ All Q
  mapAll η ⌀       = ⌀
  mapAll η (γ , a) = mapAll η γ , η a

  lastAll : ∀ {A Γ P} → All P (Γ , A) → P A
  lastAll (γ , a) = a

  initAll : ∀ {A Γ P} → All P (Γ , A) → All P Γ
  initAll (γ , a) = γ

  all : ∀ {P} → (∀ A → Dec (P A)) → (∀ Γ → Dec (All P Γ))
  all P? ⌀       = yes ⌀
  all P? (Γ , A) with P? A
  …             | yes a = mapDec (_, a) initAll (all P? Γ)
  …             | no ¬a = no (¬a ∘ lastAll)


-- Predicate-based possibility.

module _ {U : Set} where
  data Any (P : Pred U) : Pred (Cx U) where
    top : ∀ {A Γ} → P A → Any P (Γ , A)
    pop : ∀ {A Γ} → Any P Γ → Any P (Γ , A)

  find : ∀ {Γ P} → Any P Γ → Σ U (λ A → P A)
  find (top {A} a) = A , a
  find (pop i)     = find i

  mapAny : ∀ {P Q} → P ⊆ᴾ Q → Any P ⊆ᴾ Any Q
  mapAny η (top a) = top (η a)
  mapAny η (pop γ) = pop (mapAny η γ)

  initAny : ∀ {A Γ P} → Not (P A) → Any P (Γ , A) → Any P Γ
  initAny ¬a (top a) = a ↯ ¬a
  initAny ¬a (pop γ) = γ

  any : ∀ {P} → (∀ A → Dec (P A)) → (∀ Γ → Dec (Any P Γ))
  any P? ⌀       = no λ ()
  any P? (Γ , A) with P? A
  …             | yes a = yes (top a)
  …             | no ¬a = mapDec pop (initAny ¬a) (any P? Γ)
