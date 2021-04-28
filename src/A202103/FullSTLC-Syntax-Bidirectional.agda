module A202103.FullSTLC-Syntax-Bidirectional where

open import A202103.FullSTLC-Syntax public
import A202103.GenericSubstitution

------------------------------------------------------------------------------

mutual
  infix 3 _⊢≪_
  data _⊢≪_ (Γ : List Type) : Type → Set where
    lam    : ∀ {A B} → Γ , A ⊢≪ B → Γ ⊢≪ A ⊃ B
    unit   : Γ ⊢≪ ⊤
    pair   : ∀ {A B} → Γ ⊢≪ A → Γ ⊢≪ B → Γ ⊢≪ A ∧ B
    left   : ∀ {A B} → Γ ⊢≪ A → Γ ⊢≪ A ∨ B
    right  : ∀ {A B} → Γ ⊢≪ B → Γ ⊢≪ A ∨ B
    letsum : ∀ {A B C} → Γ ⊢≫ A ∨ B → Γ , A ⊢≪ C → Γ , B ⊢≪ C → Γ ⊢≪ C
    abort  : ∀ {C} → Γ ⊢≫ ⊥ → Γ ⊢≪ C
    ch     : Γ ⊢≫ ◦ → Γ ⊢≪ ◦

  infix 3 _⊢≫_
  data _⊢≫_ (Γ : List Type) : Type → Set where
    var : ∀ {A} → Γ ∋ A → Γ ⊢≫ A
    app : ∀ {A B} → Γ ⊢≫ A ⊃ B → Γ ⊢≪ A → Γ ⊢≫ B
    fst : ∀ {A B} → Γ ⊢≫ A ∧ B → Γ ⊢≫ A
    snd : ∀ {A B} → Γ ⊢≫ A ∧ B → Γ ⊢≫ B

------------------------------------------------------------------------------

mutual
  rench : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢≪ A → Γ′ ⊢≪ A
  rench η (lam t)           = lam (rench (liftr η) t)
  rench η unit              = unit
  rench η (pair t₁ t₂)      = pair (rench η t₁) (rench η t₂)
  rench η (left t)          = left (rench η t)
  rench η (right t)         = right (rench η t)
  rench η (letsum t₁ t₂ t₃) = letsum (renth η t₁) (rench (liftr η) t₂) (rench (liftr η) t₃)
  rench η (abort t)         = abort (renth η t)
  rench η (ch t)            = ch (renth η t)

  renth : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢≫ A → Γ′ ⊢≫ A
  renth η (var x)     = var (η x)
  renth η (app t₁ t₂) = app (renth η t₁) (rench η t₂)
  renth η (fst t)     = fst (renth η t)
  renth η (snd t)     = snd (renth η t)

mutual
  id-rench : ∀ {Γ A} (t : Γ ⊢≪ A) →
             rench idr t ≡ t
  id-rench (lam t)           = lam & id-rench-lift t
  id-rench unit              = refl
  id-rench (pair t₁ t₂)      = pair & id-rench t₁ ⊗ id-rench t₂
  id-rench (left t)          = left & id-rench t
  id-rench (right t)         = right & id-rench t
  id-rench (letsum t₁ t₂ t₃) = letsum & id-renth t₁ ⊗ id-rench-lift t₂ ⊗ id-rench-lift t₃
  id-rench (abort t)         = abort & id-renth t
  id-rench (ch t)            = ch & id-renth t

  id-rench-lift : ∀ {Γ A C} (t : Γ , C ⊢≪ A) → rench (liftr idr) t ≡ t
  id-rench-lift t = flip rench t & fu′ (fu id-liftr)
                  ⋮ id-rench t

  id-renth : ∀ {Γ A} (t : Γ ⊢≫ A) →
             renth idr t ≡ t
  id-renth (var x)     = refl
  id-renth (app t₁ t₂) = app & id-renth t₁ ⊗ id-rench t₂
  id-renth (fst t)     = fst & id-renth t
  id-renth (snd t)     = snd & id-renth t

mutual
  comp-rench-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢≪ A) →
                    rench (renr η′ η) t ≡ rench η′ (rench η t)
  comp-rench-renr η′ η (lam t)           = lam & comp-rench-renr-lift η′ η t
  comp-rench-renr η′ η unit              = refl
  comp-rench-renr η′ η (pair t₁ t₂)      = pair & comp-rench-renr η′ η t₁ ⊗ comp-rench-renr η′ η t₂
  comp-rench-renr η′ η (left t)          = left & comp-rench-renr η′ η t
  comp-rench-renr η′ η (right t)         = right & comp-rench-renr η′ η t
  comp-rench-renr η′ η (letsum t₁ t₂ t₃) = letsum & comp-renth-renr η′ η t₁
                                                  ⊗ comp-rench-renr-lift η′ η t₂
                                                  ⊗ comp-rench-renr-lift η′ η t₃
  comp-rench-renr η′ η (abort t)         = abort & comp-renth-renr η′ η t
  comp-rench-renr η′ η (ch t)            = ch & comp-renth-renr η′ η t

  comp-rench-renr-lift : ∀ {Γ Γ′ Γ″ A C} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ , C ⊢≪ A) →
                         rench (liftr (renr η′ η)) t ≡ rench (liftr η′) (rench (liftr η) t)
  comp-rench-renr-lift η′ η t = flip rench t & fu′ (fu (comp-liftr-renr η′ η))
                              ⋮ comp-rench-renr (liftr η′) (liftr η) t

  comp-renth-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢≫ A) →
                    renth (renr η′ η) t ≡ renth η′ (renth η t)
  comp-renth-renr η′ η (var x)     = refl
  comp-renth-renr η′ η (app t₁ t₂) = app & comp-renth-renr η′ η t₁ ⊗ comp-rench-renr η′ η t₂
  comp-renth-renr η′ η (fst t)     = fst & comp-renth-renr η′ η t
  comp-renth-renr η′ η (snd t)     = snd & comp-renth-renr η′ η t

Rench : ∀ A → Presheaf REN (_⊢≪ A)
Rench A = record
            { φ     = rench
            ; idφ   = fu id-rench
            ; compφ = λ η η′ → fu (comp-rench-renr η′ η)
            }

Renth : ∀ A → Presheaf REN (_⊢≫ A)
Renth A = record
            { φ     = renth
            ; idφ   = fu id-renth
            ; compφ = λ η η′ → fu (comp-renth-renr η′ η)
            }

rsth : RenSpec
rsth = record
         { _⊢_           = _⊢≫_
         ; ren           = renth
         ; id-ren        = id-renth
         ; comp-ren-renr = comp-renth-renr
         ; var           = var
         ; comp-ren-var  = λ η x → refl
         }

------------------------------------------------------------------------------

open A202103.GenericSubstitution rsth public
  using ()
  renaming (_⊢*_ to _⊢≫*_ ; ids to idths ; rens to renths)

------------------------------------------------------------------------------

mutual
  -- To embed a checking term (as a term).
  embch : ∀ {Γ A} → Γ ⊢≪ A → Γ ⊢ A
  embch (lam t)           = lam (embch t)
  embch unit              = unit
  embch (pair t₁ t₂)      = pair (embch t₁) (embch t₂)
  embch (left t)          = left (embch t)
  embch (right t)         = right (embch t)
  embch (letsum t₁ t₂ t₃) = letsum (embth t₁) (embch t₂) (embch t₃)
  embch (abort t)         = abort (embth t)
  embch (ch t)            = embth t

  -- To embed a synthesizing term (as a term).
  embth : ∀ {Γ A} → Γ ⊢≫ A → Γ ⊢ A
  embth (var x)     = var x
  embth (app t₁ t₂) = app (embth t₁) (embch t₂)
  embth (fst t)     = fst (embth t)
  embth (snd t)     = snd (embth t)

mutual
  -- Naturality of embedding a checking term wrt. renaming.
  nat-embch : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (t : Γ ⊢≪ A) →
              embch (rench η t) ≡ ren η (embch t)
  nat-embch η (lam t)           = lam & nat-embch (liftr η) t
  nat-embch η unit              = refl
  nat-embch η (pair t₁ t₂)      = pair & nat-embch η t₁ ⊗ nat-embch η t₂
  nat-embch η (left t)          = left & nat-embch η t
  nat-embch η (right t)         = right & nat-embch η t
  nat-embch η (letsum t₁ t₂ t₃) = letsum & nat-embth η t₁ ⊗ nat-embch (liftr η) t₂ ⊗ nat-embch (liftr η) t₃
  nat-embch η (abort t)         = abort & nat-embth η t
  nat-embch η (ch t)            = nat-embth η t

  -- Naturality of embedding a synthesizing term wrt. renaming.
  nat-embth : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (t : Γ ⊢≫ A) →
              embth (renth η t) ≡ ren η (embth t)
  nat-embth η (var x)     = refl
  nat-embth η (app t₁ t₂) = app & nat-embth η t₁ ⊗ nat-embch η t₂
  nat-embth η (fst t)     = fst & nat-embth η t
  nat-embth η (snd t)     = snd & nat-embth η t

-- Embedding a checking term yields a natural transformation.
Embch : ∀ A → NatTrans (Rench A) (Ren A)
Embch A = record
            { α    = embch
            ; natα = λ η → fu (nat-embch η)
            }

-- Embedding a synthesizing term yields a natural transformation.
Embth : ∀ A → NatTrans (Renth A) (Ren A)
Embth A = record
            { α    = embth
            ; natα = λ η → fu (nat-embth η)
            }

------------------------------------------------------------------------------
