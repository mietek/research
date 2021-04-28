module A202103.FullSTLC-Syntax where

open import A202103.Prelude public
open import A202103.Category public
open import A202103.List public
open import A202103.GenericRenaming public
import A202103.GenericSubstitution
import A202103.GenericSubstitution-Part2
import A202103.GenericSubstitution-Part3

------------------------------------------------------------------------------

infixr 7 _⊃_
data Type : Set where
  ◦   : Type
  _⊃_ : Type → Type → Type
  ⊤   : Type
  _∧_ : Type → Type → Type
  _∨_ : Type → Type → Type
  ⊥   : Type

infix 3 _⊢_
data _⊢_ (Γ : List Type) : Type → Set where
  var    : ∀ {A} → Γ ∋ A → Γ ⊢ A
  lam    : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A ⊃ B
  app    : ∀ {A B} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B
  unit   : Γ ⊢ ⊤
  pair   : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  fst    : ∀ {A B} → Γ ⊢ A ∧ B → Γ ⊢ A
  snd    : ∀ {A B} → Γ ⊢ A ∧ B → Γ ⊢ B
  left   : ∀ {A B} → Γ ⊢ A → Γ ⊢ A ∨ B
  right  : ∀ {A B} → Γ ⊢ B → Γ ⊢ A ∨ B
  letsum : ∀ {A B C} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
  abort  : ∀ {C} → Γ ⊢ ⊥ → Γ ⊢ C

------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢ A → Γ′ ⊢ A
ren η (var x)           = var (η x)
ren η (lam t)           = lam (ren (liftr η) t)
ren η (app t₁ t₂)       = app (ren η t₁) (ren η t₂)
ren η unit              = unit
ren η (pair t₁ t₂)      = pair (ren η t₁) (ren η t₂)
ren η (fst t)           = fst (ren η t)
ren η (snd t)           = snd (ren η t)
ren η (left t)          = left (ren η t)
ren η (right t)         = right (ren η t)
ren η (letsum t₁ t₂ t₃) = letsum (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃)
ren η (abort t)         = abort (ren η t)

mutual
  id-ren : ∀ {Γ A} (t : Γ ⊢ A) →
           ren idr t ≡ t
  id-ren (var x)           = refl
  id-ren (lam t)           = lam & id-ren-lift t
  id-ren (app t₁ t₂)       = app & id-ren t₁ ⊗ id-ren t₂
  id-ren unit              = refl
  id-ren (pair t₁ t₂)      = pair & id-ren t₁ ⊗ id-ren t₂
  id-ren (fst t)           = fst & id-ren t
  id-ren (snd t)           = snd & id-ren t
  id-ren (left t)          = left & id-ren t
  id-ren (right t)         = right & id-ren t
  id-ren (letsum t₁ t₂ t₃) = letsum & id-ren t₁ ⊗ id-ren-lift t₂ ⊗ id-ren-lift t₃
  id-ren (abort t)         = abort & id-ren t

  id-ren-lift : ∀ {Γ A C} (t : Γ , C ⊢ A) → ren (liftr idr) t ≡ t
  id-ren-lift t = flip ren t & fu′ (fu id-liftr)
                ⋮ id-ren t

mutual
  comp-ren-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢ A) →
                  ren (renr η′ η) t ≡ ren η′ (ren η t)
  comp-ren-renr η′ η (var x)           = refl
  comp-ren-renr η′ η (lam t)           = lam & comp-ren-renr-lift η′ η t
  comp-ren-renr η′ η (app t₁ t₂)       = app & comp-ren-renr η′ η t₁ ⊗ comp-ren-renr η′ η t₂
  comp-ren-renr η′ η unit              = refl
  comp-ren-renr η′ η (pair t₁ t₂)      = pair & comp-ren-renr η′ η t₁ ⊗ comp-ren-renr η′ η t₂
  comp-ren-renr η′ η (fst t)           = fst & comp-ren-renr η′ η t
  comp-ren-renr η′ η (snd t)           = snd & comp-ren-renr η′ η t
  comp-ren-renr η′ η (left t)          = left & comp-ren-renr η′ η t
  comp-ren-renr η′ η (right t)         = right & comp-ren-renr η′ η t
  comp-ren-renr η′ η (letsum t₁ t₂ t₃) = letsum & comp-ren-renr η′ η t₁
                                                ⊗ comp-ren-renr-lift η′ η t₂
                                                ⊗ comp-ren-renr-lift η′ η t₃
  comp-ren-renr η′ η (abort t)         = abort & comp-ren-renr η′ η t

  comp-ren-renr-lift : ∀ {Γ Γ′ Γ″ A C} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ , C ⊢ A) →
                       ren (liftr (renr η′ η)) t ≡ ren (liftr η′) (ren (liftr η) t)
  comp-ren-renr-lift η′ η t = flip ren t & fu′ (fu (comp-liftr-renr η′ η))
                            ⋮ comp-ren-renr (liftr η′) (liftr η) t

Ren : ∀ A → Presheaf REN (_⊢ A)
Ren A = record
          { φ     = ren
          ; idφ   = fu id-ren
          ; compφ = λ η η′ → fu (comp-ren-renr η′ η)
          }

private
  rs : RenSpec
  rs = record
         { _⊢_           = _⊢_
         ; ren           = ren
         ; id-ren        = id-ren
         ; comp-ren-renr = comp-ren-renr
         ; var           = var
         ; comp-ren-var  = λ η x → refl
         }

------------------------------------------------------------------------------

open A202103.GenericSubstitution rs public

sub : ∀ {Γ Ξ A} → Γ ⊢* Ξ → Ξ ⊢ A → Γ ⊢ A
sub σ (var x)           = σ x
sub σ (lam t)           = lam (sub (lifts σ) t)
sub σ (app t₁ t₂)       = app (sub σ t₁) (sub σ t₂)
sub σ unit              = unit
sub σ (pair t₁ t₂)      = pair (sub σ t₁) (sub σ t₂)
sub σ (fst t)           = fst (sub σ t)
sub σ (snd t)           = snd (sub σ t)
sub σ (left t)          = left (sub σ t)
sub σ (right t)         = right (sub σ t)
sub σ (letsum t₁ t₂ t₃) = letsum (sub σ t₁) (sub (lifts σ) t₂) (sub (lifts σ) t₃)
sub σ (abort t)         = abort (sub σ t)

mutual
  id-sub : ∀ {Γ A} (t : Γ ⊢ A) →
           sub ids t ≡ t
  id-sub (var x)           = refl
  id-sub (lam t)           = lam & id-sub-lift t
  id-sub (app t₁ t₂)       = app & id-sub t₁ ⊗ id-sub t₂
  id-sub unit              = refl
  id-sub (pair t₁ t₂)      = pair & id-sub t₁ ⊗ id-sub t₂
  id-sub (fst t)           = fst & id-sub t
  id-sub (snd t)           = snd & id-sub t
  id-sub (left t)          = left & id-sub t
  id-sub (right t)         = right & id-sub t
  id-sub (letsum t₁ t₂ t₃) = letsum & id-sub t₁ ⊗ id-sub-lift t₂ ⊗ id-sub-lift t₃
  id-sub (abort t)         = abort & id-sub t

  id-sub-lift : ∀ {Γ A C} (t : Γ , C ⊢ A) →
                sub (lifts ids) t ≡ t
  id-sub-lift t = flip sub t & fu′ (fu id-lifts)
                ⋮ id-sub t

mutual
  comp-sub-subr : ∀ {Γ Ξ Ξ′ A} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (t : Ξ ⊢ A) →
                  sub (subr σ η) t ≡ sub σ (ren η t)
  comp-sub-subr σ η (var x)           = refl
  comp-sub-subr σ η (lam t)           = lam & comp-sub-subr-lift σ η t
  comp-sub-subr σ η (app t₁ t₂)       = app & comp-sub-subr σ η t₁ ⊗ comp-sub-subr σ η t₂
  comp-sub-subr σ η unit              = refl
  comp-sub-subr σ η (pair t₁ t₂)      = pair & comp-sub-subr σ η t₁ ⊗ comp-sub-subr σ η t₂
  comp-sub-subr σ η (fst t)           = fst & comp-sub-subr σ η t
  comp-sub-subr σ η (snd t)           = snd & comp-sub-subr σ η t
  comp-sub-subr σ η (left t)          = left & comp-sub-subr σ η t
  comp-sub-subr σ η (right t)         = right & comp-sub-subr σ η t
  comp-sub-subr σ η (letsum t₁ t₂ t₃) = letsum & comp-sub-subr σ η t₁
                                               ⊗ comp-sub-subr-lift σ η t₂
                                               ⊗ comp-sub-subr-lift σ η t₃
  comp-sub-subr σ η (abort t)         = abort & comp-sub-subr σ η t

  comp-sub-subr-lift : ∀ {Γ Ξ Ξ′ A C} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (t : Ξ , C ⊢ A) →
                       sub (lifts (subr σ η)) t ≡ sub (lifts σ) (ren (liftr η) t)
  comp-sub-subr-lift σ η t = flip sub t & fu′ (fu (comp-lifts-subr σ η))
                           ⋮ comp-sub-subr (lifts σ) (liftr η) t

mutual
  comp-sub-rens : ∀ {Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (t : Ξ ⊢ A) →
                  sub (rens η σ) t ≡ ren η (sub σ t)
  comp-sub-rens η σ (var x)           = comp-subi-rens η σ x
  comp-sub-rens η σ (lam t)           = lam & comp-sub-rens-lift η σ t
  comp-sub-rens η σ (app t₁ t₂)       = app & comp-sub-rens η σ t₁ ⊗ comp-sub-rens η σ t₂
  comp-sub-rens η σ unit              = refl
  comp-sub-rens η σ (pair t₁ t₂)      = pair & comp-sub-rens η σ t₁ ⊗ comp-sub-rens η σ t₂
  comp-sub-rens η σ (fst t)           = fst & comp-sub-rens η σ t
  comp-sub-rens η σ (snd t)           = snd & comp-sub-rens η σ t
  comp-sub-rens η σ (left t)          = left & comp-sub-rens η σ t
  comp-sub-rens η σ (right t)         = right & comp-sub-rens η σ t
  comp-sub-rens η σ (letsum t₁ t₂ t₃) = letsum & comp-sub-rens η σ t₁
                                               ⊗ comp-sub-rens-lift η σ t₂
                                               ⊗ comp-sub-rens-lift η σ t₃
  comp-sub-rens η σ (abort t)         = abort & comp-sub-rens η σ t

  comp-sub-rens-lift : ∀ {Γ Γ′ Ξ A C} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (t : Ξ , C ⊢ A) →
                       sub (lifts (rens η σ)) t ≡ ren (liftr η) (sub (lifts σ) t)
  comp-sub-rens-lift η σ t = flip sub t & fu′ (fu (comp-lifts-rens η σ))
                           ⋮ comp-sub-rens (liftr η) (lifts σ) t

private
  ss : SubSpec
  ss = record
         { sub           = sub
         ; id-sub        = id-sub
         ; comp-sub-subr = comp-sub-subr
         ; comp-sub-rens = comp-sub-rens
         ; comp-sub-var  = λ σ x → refl
         }

------------------------------------------------------------------------------

open A202103.GenericSubstitution-Part2 ss public

mutual
  comp-sub-subs : ∀ {Γ Ξ Ψ A} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (t : Ψ ⊢ A) →
                  sub (subs σ′ σ) t ≡ sub σ′ (sub σ t)
  comp-sub-subs σ′ σ (var x)           = comp-subi-subs σ′ σ x
  comp-sub-subs σ′ σ (lam t)           = lam & comp-sub-subs-lift σ′ σ t
  comp-sub-subs σ′ σ (app t₁ t₂)       = app & comp-sub-subs σ′ σ t₁ ⊗ comp-sub-subs σ′ σ t₂
  comp-sub-subs σ′ σ unit              = refl
  comp-sub-subs σ′ σ (pair t₁ t₂)      = pair & comp-sub-subs σ′ σ t₁ ⊗ comp-sub-subs σ′ σ t₂
  comp-sub-subs σ′ σ (fst t)           = fst & comp-sub-subs σ′ σ t
  comp-sub-subs σ′ σ (snd t)           = snd & comp-sub-subs σ′ σ t
  comp-sub-subs σ′ σ (left t)          = left & comp-sub-subs σ′ σ t
  comp-sub-subs σ′ σ (right t)         = right & comp-sub-subs σ′ σ t
  comp-sub-subs σ′ σ (letsum t₁ t₂ t₃) = letsum & comp-sub-subs σ′ σ t₁
                                                ⊗ comp-sub-subs-lift σ′ σ t₂
                                                ⊗ comp-sub-subs-lift σ′ σ t₃
  comp-sub-subs σ′ σ (abort t)         = abort & comp-sub-subs σ′ σ t

  comp-sub-subs-lift : ∀ {Γ Ξ Ψ A C} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (t : Ψ , C ⊢ A) →
                       sub (lifts (subs σ′ σ)) t ≡ sub (lifts σ′) (sub (lifts σ) t)
  comp-sub-subs-lift σ′ σ t = flip sub t & fu′ (fu (comp-lifts-subs σ′ σ))
                            ⋮ comp-sub-subs (lifts σ′) (lifts σ) t

private
  ss2 : SubSpec-Part2
  ss2 = record
          { comp-sub-subs = comp-sub-subs
          }

------------------------------------------------------------------------------

open A202103.GenericSubstitution-Part3 ss2 public

------------------------------------------------------------------------------
