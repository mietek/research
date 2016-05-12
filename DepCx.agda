module DepCx (Hyp : Set) (⟦_⟧H : Hyp → Set) where
  open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
  open import Data.Unit renaming (⊤ to Unit)
  open import Function using () renaming (_∘_ to _○_)

  mutual
    infixl 2 _,_
    data DepCx : Set where
      ∅   : DepCx
      _,_ : (Γ : DepCx) → (F : ⟦ Γ ⟧C → Hyp) → DepCx

    ⟦_⟧C : DepCx → Set
    ⟦ ∅ ⟧C     = Unit
    ⟦ Γ , F ⟧C = Σ ⟦ Γ ⟧C (λ γ → ⟦ F γ ⟧H)

  len : DepCx → Nat
  len ∅       = zero
  len (Γ , F) = suc (len Γ)

  data _∋_ : (Γ : DepCx) (F : ⟦ Γ ⟧C → Hyp) → Set where
    here : ∀{Γ F} → (Γ , F) ∋ (F ○ proj₁)
    pop  : ∀{Γ F E} → Γ ∋ F → (Γ , E) ∋ (F ○ proj₁)

  ⟦_⟧∋ : ∀{Γ F} → Γ ∋ F → (γ : ⟦ Γ ⟧C) → ⟦ F γ ⟧H
  ⟦ here ⟧∋  (γ , a) = a
  ⟦ pop i ⟧∋ (γ , b) = ⟦ i ⟧∋ γ

  ix : ∀{Γ F} → Γ ∋ F → Fin (len Γ)
  ix here    = zero
  ix (pop i) = suc (ix i)

  𝟎 : ∀{Γ F} → (Γ , F) ∋ (F ○ proj₁)
  𝟎 = here

  𝟏 : ∀{Γ F G} → ((Γ , F) , G) ∋ (F ○ proj₁ ○ proj₁)
  𝟏 = pop 𝟎

  𝟐 : ∀{Γ F G H} → (((Γ , F) , G) , H) ∋ (F ○ proj₁ ○ proj₁ ○ proj₁)
  𝟐 = pop 𝟏

  𝟑 : ∀{Γ F G H I} → ((((Γ , F) , G) , H) , I) ∋ (F ○ proj₁ ○ proj₁ ○ proj₁ ○ proj₁)
  𝟑 = pop 𝟐
