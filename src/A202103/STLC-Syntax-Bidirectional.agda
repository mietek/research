module A202103.STLC-Syntax-Bidirectional where

open import A202103.STLC-Syntax public
import A202103.GenericSubstitution

------------------------------------------------------------------------------

mutual
  -- Checking terms.
  infix 3 _⊢≪_
  data _⊢≪_ (Γ : List Type) : Type → Set where
    lam : ∀ {A B} → Γ , A ⊢≪ B → Γ ⊢≪ A ⊃ B
    ch  : Γ ⊢≫ ◦ → Γ ⊢≪ ◦

  -- Synthesizing terms.
  infix 3 _⊢≫_
  data _⊢≫_ (Γ : List Type) : Type → Set where
    var : ∀ {A} → Γ ∋ A → Γ ⊢≫ A
    app : ∀ {A B} → Γ ⊢≫ A ⊃ B → Γ ⊢≪ A → Γ ⊢≫ B

------------------------------------------------------------------------------

mutual
  -- To rename (all indices in) a checking term.
  rench : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢≪ A → Γ′ ⊢≪ A
  rench η (lam t) = lam (rench (liftr η) t)
  rench η (ch t)  = ch (renth η t)

  -- To rename (all indices in) a synthesizing term.
  renth : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢≫ A → Γ′ ⊢≫ A
  renth η (var x)     = var (η x)
  renth η (app t₁ t₂) = app (renth η t₁) (rench η t₂)

mutual
  -- Identity of renaming a checking term.
  id-rench : ∀ {Γ A} (t : Γ ⊢≪ A) →
             rench idr t ≡ t
  id-rench (lam t) = lam & ( flip rench t & fu′ (fu id-liftr)
                           ⋮ id-rench t)
  id-rench (ch t)  = ch & id-renth t

  -- Identity of renaming a synthesizing term.
  id-renth : ∀ {Γ A} (t : Γ ⊢≫ A) →
             renth idr t ≡ t
  id-renth (var x)     = refl
  id-renth (app t₁ t₂) = app & id-renth t₁ ⊗ id-rench t₂

mutual
  -- Compatibility of renaming a checking term and composing renamings.
  comp-rench-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢≪ A) →
                    rench (renr η′ η) t ≡ rench η′ (rench η t)
  comp-rench-renr η′ η (lam t) = lam & ( flip rench t & fu′ (fu (comp-liftr-renr η′ η))
                                       ⋮ comp-rench-renr (liftr η′) (liftr η) t)
  comp-rench-renr η′ η (ch t)  = ch & comp-renth-renr η′ η t

  -- Compatibility of renaming a synthesizing term and composing renamings.
  comp-renth-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢≫ A) →
                    renth (renr η′ η) t ≡ renth η′ (renth η t)
  comp-renth-renr η′ η (var x)     = refl
  comp-renth-renr η′ η (app t₁ t₂) = app & comp-renth-renr η′ η t₁ ⊗ comp-rench-renr η′ η t₂

-- Renaming a checking term yields a presheaf.
Rench : ∀ A → Presheaf REN (_⊢≪ A)
Rench A = record
            { φ     = rench
            ; idφ   = fu id-rench
            ; compφ = λ η η′ → fu (comp-rench-renr η′ η)
            }

-- Renaming a synthesizing term yields a presheaf.
Renth : ∀ A → Presheaf REN (_⊢≫ A)
Renth A = record
            { φ     = renth
            ; idφ   = fu id-renth
            ; compφ = λ η η′ → fu (comp-renth-renr η′ η)
            }

-- TODO: Close to a presheaf.
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
  embch (lam t) = lam (embch t)
  embch (ch t)  = embth t

  -- To embed a synthesizing term (as a term).
  embth : ∀ {Γ A} → Γ ⊢≫ A → Γ ⊢ A
  embth (var x)     = var x
  embth (app t₁ t₂) = app (embth t₁) (embch t₂)

mutual
  -- Naturality of embedding a checking term wrt. renaming.
  nat-embch : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (t : Γ ⊢≪ A) →
              embch (rench η t) ≡ ren η (embch t)
  nat-embch η (lam t) = lam & nat-embch (liftr η) t
  nat-embch η (ch t)  = nat-embth η t

  -- Naturality of embedding a synthesizing term wrt. renaming.
  nat-embth : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (t : Γ ⊢≫ A) →
              embth (renth η t) ≡ ren η (embth t)
  nat-embth η (var x)     = refl
  nat-embth η (app t₁ t₂) = app & nat-embth η t₁ ⊗ nat-embch η t₂

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
