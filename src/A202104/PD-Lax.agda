module A202104.PD-Lax where

open import A202103.Prelude public
open import A202103.List public
open import A202103.GenericRenaming public

module M where
  import A202104.PD
  open A202104.PD public hiding (module ImplicitSyntax ; module ExplicitSyntax)
  open A202104.PD.ImplicitSyntax public

open M using () renaming (_⁏_⊢_true to _⁏_⊢ᴹ_true ; _⁏_⊢_poss to _⁏_⊢ᴹ_poss)

------------------------------------------------------------------------------

infixr 7 _⇒_
data Type : Set where
  α_   : ∀ (P : Atom) → Type
  _⇒_ : ∀ (A B : Type) → Type
  ○_   : ∀ (A : Type) → Type

record ValidAss : Set where
  constructor _valid
  field
    A : Type

ValidCtx = List ValidAss

mutual
  infix 3 _⊢_valid
  data _⊢_valid (Γ : ValidCtx) : Type → Set where
    var : ∀ {A} (x : Γ ∋ A valid) → Γ ⊢ A valid
    lam : ∀ {A B} → Γ , A valid ⊢ B valid → Γ ⊢ A ⇒ B valid
    app : ∀ {A B} → Γ ⊢ A ⇒ B valid → Γ ⊢ A valid → Γ ⊢ B valid
    cir : ∀ {A} → Γ ⊢ A lax → Γ ⊢ ○ A valid

  infix 3 _⊢_lax
  data _⊢_lax (Γ : ValidCtx) : Type → Set where
    ret    : ∀ {A} → Γ ⊢ A valid → Γ ⊢ A lax
    letcir : ∀ {A C} → Γ ⊢ ○ A valid → Γ , A valid ⊢ C lax → Γ ⊢ C lax

law₁ : ∀ {Γ A} → Γ ⊢ A ⇒ ○ A valid
law₁ = lam (cir (ret (var top)))

law₂ : ∀ {Γ A} → Γ ⊢ ○ ○ A ⇒ ○ A valid
law₂ = lam (cir (letcir (var top) (letcir (var top) (ret (var top)))))

law₃ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) ⇒ (○ A ⇒ ○ B) valid
law₃ = lam (lam (cir (letcir (var top) (ret (app (var (pop (pop top))) (var top))))))

⟦_⟧+ : Type → M.Type
⟦ α P ⟧+    = M.α P
⟦ A ⇒ B ⟧+ = M.□ ⟦ A ⟧+ M.⊃ ⟦ B ⟧+
⟦ ○ A ⟧+    = M.◇ M.□ ⟦ A ⟧+

⟦_⟧++ : ValidCtx → M.ValidCtx
⟦ · ⟧++          = ·
⟦ Γ , A valid ⟧++ = ⟦ Γ ⟧++ , ⟦ A ⟧+ M.valid

to-vass : ∀ {Γ A} → Γ ∋ A valid → ⟦ Γ ⟧++ ∋ ⟦ A ⟧+ M.valid
to-vass top     = top
to-vass (pop x) = pop (to-vass x)

mutual
  to-true : ∀ {Γ A} → Γ ⊢ A valid → ⟦ Γ ⟧++ ⁏ · ⊢ᴹ ⟦ A ⟧+ true
  to-true (var x)     = M.vvar (to-vass x)
  to-true (lam t)     = M.llam (to-true t)
  to-true (app t₁ t₂) = M.lapp (to-true t₁) (to-true t₂)
  to-true (cir t)     = M.cir (to-poss t)

  to-poss : ∀ {Γ A} → Γ ⊢ A lax → ⟦ Γ ⟧++ ⁏ · ⊢ᴹ M.□ ⟦ A ⟧+ poss
  to-poss (ret t)        = M.retp (M.box (to-true t))
  to-poss (letcir t₁ t₂) = M.letcir (to-true t₁) (to-poss t₂)

⟦_⟧- : M.Type → Type
⟦ M.α P ⟧-   = α P
⟦ A M.⊃ B ⟧- = ⟦ A ⟧- ⇒ ⟦ B ⟧-
⟦ M.□ A ⟧-   = ⟦ A ⟧-
⟦ M.◇ A ⟧-   = ○ ⟦ A ⟧-
