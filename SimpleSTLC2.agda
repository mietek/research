module SimpleSTLC2 where

open import Data.Empty renaming (⊥ to Ag-⊥ ; ⊥-elim to Ag-⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; raise)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit renaming (⊤ to Ag-⊤ ; tt to Ag-top)

infixr 2 _∶_
infixr 1 _⊃_
infixr 0 _⊢_∷_ _⊢_∷_∷_


-- --------------------------------------------------------------------------
--
-- Well-scoped syntax


data Tm (m : ℕ) : Set where
  var_  : Fin m → Tm m
  lam_  : Tm (suc m) → Tm m
  _$_   : Tm m → Tm m → Tm m
  ⟨_,_⟩ : Tm m → Tm m → Tm m
  fst_  : Tm m → Tm m
  snd_  : Tm m → Tm m
  !_    : Tm m → Tm m
  up_   : Tm m → Tm m
  dn_   : Tm m → Tm m
  efq_  : Tm m → Tm m
  top   : Tm m


#0 : ∀ {m} → Fin (suc m)
#0 = zero

#1 : ∀ {m} → Fin (suc (suc m))
#1 = suc #0

#2 : ∀ {m} → Fin (suc (suc (suc m)))
#2 = suc #1


-- --------------------------------------------------------------------------
--
-- Types


data Ty : Set where
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  _∶_ : Tm 0 → Ty → Ty
  ⊥  : Ty
  ⊤  : Ty


¬_ : Ty → Ty
¬ A = A ⊃ ⊥


-- --------------------------------------------------------------------------
--
-- Contexts


data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx


nat : Cx → ℕ
nat ∅       = zero
nat (Γ , x) = suc (nat Γ)


-- --------------------------------------------------------------------------
--
-- Context membership


data _∈_ (A : Ty) : Cx → Set where
  here : ∀ {Γ}
      → A ∈ (Γ , A)

  there_ : ∀ {Γ B}
      → A ∈ Γ
      → A ∈ (Γ , B)


fin : ∀ {Γ A} → A ∈ Γ → Fin (nat Γ)
fin here      = zero
fin (there i) = suc (fin i)


M#0 : ∀ {Γ A}
    → A ∈ (Γ , A)
M#0 = here

M#1 : ∀ {Γ A B}
    → A ∈ ((Γ , A) , B)
M#1 = there M#0

M#2 : ∀ {Γ A B C}
    → A ∈ (((Γ , A) , B) , C)
M#2 = there M#1


-- --------------------------------------------------------------------------
--
-- Well-typed syntax


data _⊢_∷_ (Γ : Cx) : (t : Tm (nat Γ)) → Ty → Set where
  Mvar_ : ∀ {A}
      → (i : A ∈ Γ)
      → Γ ⊢ var (fin i) ∷ A

  Mlam_ : ∀ {t : Tm (suc (nat Γ))} {A B}
      → Γ , A ⊢ t ∷ B
      → Γ ⊢ lam t ∷ (A ⊃ B)

  _M$_ : ∀ {t s : Tm (nat Γ)} {A B}
      → Γ ⊢ t ∷ (A ⊃ B)    → Γ ⊢ s ∷ A
      → Γ ⊢ t $ s ∷ B

  ⟨_M,_⟩ : ∀ {t s : Tm (nat Γ)} {A B}
      → Γ ⊢ t ∷ A    → Γ ⊢ s ∷ B
      → Γ ⊢ ⟨ t , s ⟩ ∷ (A ∧ B)

  Mfst_ : ∀ {t : Tm (nat Γ)} {A B}
      → Γ ⊢ t ∷ (A ∧ B)
      → Γ ⊢ fst t ∷ A

  Msnd_ : ∀ {t : Tm (nat Γ)} {A B}
      → Γ ⊢ t ∷ (A ∧ B)
      → Γ ⊢ snd t ∷ B

  Mup_ : ∀ {t : Tm (nat Γ)} {u : Tm 0} {A}
      → Γ ⊢ t ∷ u ∶ A
      → Γ ⊢ up t ∷ ! u ∶ u ∶ A

  Mdn_ : ∀ {t : Tm (nat Γ)} {u : Tm 0} {A}
      → Γ ⊢ t ∷ u ∶ A
      → Γ ⊢ dn t ∷ A

  Mefq_ : ∀ {t : Tm (nat Γ)} {A}
      → Γ ⊢ t ∷ ⊥
      → Γ ⊢ efq t ∷ A

  Mtop : Γ ⊢ top ∷ ⊤


data _⊢_∷_∷_ (Γ : Cx) : (t₂ t : Tm (nat Γ)) → Ty → Set where
  MMvar_ : ∀ {A}
      → (i : A ∈ Γ)
      → Γ ⊢ var (fin i) ∷ var (fin i) ∷ A

  MMlam_ : ∀ {t₂ t : Tm (suc (nat Γ))} {A B}
      → Γ , A ⊢ t₂ ∷ t ∷ B
      → Γ ⊢ lam t₂ ∷ lam t ∷ (A ⊃ B)

  _MM$_ : ∀ {t₂ t s₂ s : Tm (nat Γ)} {A B}
      → Γ ⊢ t₂ ∷ t ∷ (A ⊃ B)    → Γ ⊢ s₂ ∷ s ∷ A
      → Γ ⊢ t₂ $ s₂ ∷ t $ s ∷ B

  ⟨_MM,_⟩ : ∀ {t₂ t s₂ s : Tm (nat Γ)} {A B}
      → Γ ⊢ t₂ ∷ t ∷ A    → Γ ⊢ s₂ ∷ s ∷ B
      → Γ ⊢ ⟨ t₂ , s₂ ⟩ ∷ ⟨ t , s ⟩ ∷ (A ∧ B)

  MMfst_ : ∀ {t₂ t : Tm (nat Γ)} {A B}
      → Γ ⊢ t₂ ∷ t ∷ (A ∧ B)
      → Γ ⊢ fst t₂ ∷ fst t ∷ A

  MMsnd_ : ∀ {t₂ t : Tm (nat Γ)} {A B}
      → Γ ⊢ t₂ ∷ t ∷ (A ∧ B)
      → Γ ⊢ snd t₂ ∷ snd t ∷ B

  MMup_ : ∀ {t₂ t : Tm (nat Γ)} {u : Tm 0} {A}
      → Γ ⊢ t₂ ∷ t ∷ u ∶ A
      → Γ ⊢ up t₂ ∷ up t ∷ ! u ∶ u ∶ A

  MMdn_ : ∀ {t₂ t : Tm (nat Γ)} {u : Tm 0} {A}
      → Γ ⊢ t₂ ∷ t ∷ u ∶ A
      → Γ ⊢ dn t₂ ∷ dn t ∷ A

  MMefq_ : ∀ {t₂ t : Tm (nat Γ)} {A}
      → Γ ⊢ t₂ ∷ t ∷ ⊥
      → Γ ⊢ efq t₂ ∷ efq t ∷ A

  MMtop : Γ ⊢ top ∷ top ∷ ⊤


data _⊢_∷_∷_∷_ (Γ : Cx) : (t₃ t₂ t : Tm (nat Γ)) → Ty → Set where


-- --------------------------------------------------------------------------
--
-- Semantics


{-weak : ∀ {m}
    → (k : ℕ)    → Tm (0 + m)
    → Tm (k + m)
weak {m} k (var x) = var raise k x
weak k (lam t) = {!!}
weak k (t $ t₁) = {!!}
weak k ⟨ t , t₁ ⟩ = {!!}
weak k (fst t) = {!!}
weak k (snd t) = {!!}
weak k (! t) = {!!}
weak k (up t) = {!!}
weak k (dn t) = {!!}
weak k (efq t) = {!!}
weak k top = {!!}


weak⊢ : ∀ {Γ} {t : Tm 0} {A}
    → ∅ ⊢ t ∷ A
    → Γ ⊢ weak (nat Γ) t ∷ A
weak⊢ = {!!}-}


⟦_⟧T : Ty → Set
⟦ A ⊃ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
⟦ A ∧ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ t ∶ A ⟧T = ∅ ⊢ t ∷ A
⟦ ⊤ ⟧T    = Ag-⊤
⟦ ⊥ ⟧T    = Ag-⊥


⟦_⟧C : Cx → (Ty → Set) → Set
⟦ ∅ ⟧C     V = Ag-⊤
⟦ Γ , A ⟧C V = ⟦ Γ ⟧C V × V A


⟦_⟧∈ : ∀ {Γ V A} → A ∈ Γ → ⟦ Γ ⟧C V → V A
⟦ here ⟧∈    (γ , a) = a
⟦ there i ⟧∈ (γ , b) = ⟦ i ⟧∈ γ


quot : ∀ {Γ} {t : Tm (nat Γ)} {A}
    → Γ ⊢ t ∷ A
    → Tm (nat Γ)
quot (Mvar_ i)  = var fin i
quot (Mlam D)   = lam quot D
quot (D M$ E)   = quot D $ quot E
quot ⟨ D M, E ⟩ = ⟨ quot D , quot E ⟩
quot (Mfst D)   = fst quot D
quot (Msnd D)   = snd quot D
quot (Mup D)    = up (quot D)
quot (Mdn D)    = dn (quot D)
quot (Mefq D)   = efq quot D
quot Mtop       = top

Mquot : ∀ {Γ} {t₂ t : Tm (nat Γ)} {A}
    → Γ ⊢ t₂ ∷ t ∷ A
    → Tm (nat Γ)
Mquot = {!!}


lift : ∀{Γ A} {t : Tm (nat Γ)}
    → (D : Γ ⊢ t ∷ A)
    → Γ ⊢ quot D ∷ t ∷ A
lift (Mvar i)   = MMvar i
lift (Mlam D)   = MMlam lift D
lift (D M$ E)   = lift D MM$ lift E
lift ⟨ D M, E ⟩ = ⟨ lift D MM, lift E ⟩
lift (Mfst D)   = MMfst lift D
lift (Msnd D)   = MMsnd lift D
lift (Mup D)    = MMup lift D
lift (Mdn D)    = MMdn lift D
lift (Mefq D)   = MMefq lift D
lift Mtop       = MMtop

Mlift : ∀ {Γ} {t₂ t : Tm (nat Γ)} {A}
    → (D : Γ ⊢ t₂ ∷ t ∷ A)
    → Γ ⊢ Mquot D ∷ t₂ ∷ t ∷ A
Mlift = {!!}


drop : ∀ {Γ} {t₂ t : Tm (nat Γ)} {A}
    → Γ ⊢ t₂ ∷ t ∷ A
    → Γ ⊢ t ∷ A
drop (MMvar i)   = Mvar i
drop (MMlam D)   = Mlam drop D
drop (D MM$ E)   = drop D M$ drop E
drop ⟨ D MM, E ⟩ = ⟨ drop D M, drop E ⟩
drop (MMfst D)   = Mfst drop D
drop (MMsnd D)   = Msnd drop D
drop (MMup D)    = Mup drop D
drop (MMdn D)    = Mdn drop D
drop (MMefq D)   = Mefq drop D
drop MMtop       = Mtop

Mdrop : ∀ {Γ} {t₃ t₂ t : Tm (nat Γ)} {A}
    → Γ ⊢ t₃ ∷ t₂ ∷ t ∷ A
    → Γ ⊢ t₂ ∷ t ∷ A
Mdrop = {!!}


pack : ∀ {t : Tm 0} {u : Tm 0} {A}
    → ∅ ⊢ t ∷ u ∷ A
    → ∅ ⊢ t ∷ u ∶ A
pack = {!!}

unpack : ∀ {t u : Tm 0} {A}
    → ∅ ⊢ t ∷ u ∶ A
    → ∅ ⊢ t ∷ u ∷ A
unpack = {!!}


check : ∀ {Γ} {t : Tm (nat Γ)} {u : Tm 0} {A}
    → Γ ⊢ t ∷ u ∶ A
    → ∅ ⊢ (! u) ∷ u ∶ A
check = {!!}


mutual
  ⟦_⟧ : ∀ {Γ} {t : Tm (nat Γ)} {A}
      → Γ ⊢ t ∷ A    → ⟦ Γ ⟧C ⟦_⟧T
      → ⟦ A ⟧T
  ⟦ Mvar i ⟧ γ     = ⟦ i ⟧∈ γ
  ⟦ Mlam D ⟧ γ     = λ a → ⟦ D ⟧ (γ , a)
  ⟦ D M$ E ⟧ γ     = ⟦ D ⟧ γ (⟦ E ⟧ γ)
  ⟦ ⟨ D M, E ⟩ ⟧ γ = ⟦ D ⟧ γ , ⟦ E ⟧ γ
  ⟦ Mfst D ⟧ γ     = proj₁ (⟦ D ⟧ γ)
  ⟦ Msnd D ⟧ γ     = proj₂ (⟦ D ⟧ γ)
  ⟦ Mup D ⟧ γ      = check D
  ⟦ Mdn D ⟧ γ      = M⟦ unpack {!!} ⟧ γ
  ⟦ Mefq D ⟧ γ     = Ag-⊥-elim (⟦ D ⟧ γ)
  ⟦ Mtop ⟧   γ     = Ag-top

  M⟦_⟧ : ∀ {Γ} {t₂ t : Tm 0} {A}
      → ∅ ⊢ t₂ ∷ t ∷ A    → ⟦ Γ ⟧C ⟦_⟧T
      → ⟦ A ⟧T
  M⟦_⟧ = {!!}


{-
  Mup_ : ∀ {t u : Tm (nat Γ)} {A}
      → Γ ⊢ t ∷ u ∶ A
      → Γ ⊢ up t ∷ ! u ∶ u ∶ A

  Mdn_ : ∀ {t u : Tm (nat Γ)} {A}
      → Γ ⊢ t ∷ u ∶ A
      → Γ ⊢ dn t ∷ A
-}

-- --------------------------------------------------------------------------
--
-- Example


module Tms where
  -- ∅ ⊢ B ⊃ A ⊃ A
  H : ∀ {Γ} → Tm (nat Γ)
  H = lam lam var #0

  -- ∅ ⊢ A ⊃ A
  I : ∀ {Γ} → Tm (nat Γ)
  I = lam var #0

  -- A ⊢ A
  I′ : ∀ {Γ} → Tm (suc (nat Γ))
  I′ = var #0

  -- ∅ ⊢ A ⊃ B ⊃ A
  K : ∀ {Γ} → Tm (nat Γ)
  K = lam lam var #1

  -- ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S : ∀ {Γ} → Tm (nat Γ)
  S = lam lam lam ((var #2 $ var #0) $ (var #1 $ var #0))


module MTms where
  H : ∀ {Γ A B}
      → Γ ⊢ Tms.H ∷ B ⊃ A ⊃ A
  H = Mlam Mlam Mvar M#0

  I : ∀ {Γ A}
      → Γ ⊢ Tms.I ∷ A ⊃ A
  I = Mlam Mvar M#0

  I′ : ∀ {Γ A}
      → Γ , A ⊢ Tms.I′ ∷ A
  I′ = Mvar M#0

  K : ∀ {Γ A B}
      → Γ ⊢ Tms.K ∷ A ⊃ B ⊃ A
  K = Mlam Mlam Mvar M#1

  S : ∀ {Γ A B C}
      → Γ ⊢ Tms.S ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = Mlam Mlam Mlam ((Mvar M#2 M$ Mvar M#0) M$ (Mvar M#1 M$ Mvar M#0))


module MMTms where
  H : ∀ {Γ A B}
      → Γ ⊢ Tms.H ∷ Tms.H ∷ B ⊃ A ⊃ A
  H = lift MTms.H

  I : ∀ {Γ A}
      → Γ ⊢ Tms.I ∷ Tms.I ∷ A ⊃ A
  I = lift MTms.I

  I′ : ∀ {Γ A}
      → Γ , A ⊢ Tms.I′ ∷ Tms.I′ ∷ A
  I′ = lift MTms.I′

  K : ∀ {Γ A B}
      → Γ ⊢ Tms.K ∷ Tms.K ∷ A ⊃ B ⊃ A
  K = lift MTms.K

  S : ∀ {Γ A B C}
      → Γ ⊢ Tms.S ∷ Tms.S ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = lift MTms.S


module S4 where
  K : ∀ {Γ A B f x}
      → Γ ⊢ lam lam (var #1 $ var #0) ∷ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f $ x) ∶ B
  K = Mlam Mlam {!!}

  T : ∀ {Γ A x}
      → Γ ⊢ lam dn var #0 ∷ (x ∶ A ⊃ A)
  T = Mlam Mdn Mvar M#0

  #4 : ∀ {Γ A x}
      → Γ ⊢ lam up var #0 ∷ (x ∶ A ⊃ ! x ∶ x ∶ A)
  #4 = Mlam Mup Mvar M#0

  X1 : ∀ {Γ A B x y}
      → Γ ⊢ lam lam up ⟨ var #1 , var #0 ⟩ ∷ (x ∶ A ⊃ y ∶ B ⊃ ! ⟨ x , y ⟩ ∶ ⟨ x , y ⟩ ∶ (A ∧ B))
  X1 = Mlam Mlam Mup {!!}

module Example1 where
  E11 : ∀ {Γ A x}
      → Γ ⊢ lam dn var #0 ∷ (x ∶ A ⊃ A)
  E11 = Mlam Mdn Mvar M#0

  E13 : ∀ {Γ A B}
      → Γ ⊢ lam lam ⟨ var #1 , var #0 ⟩ ∷ lam lam ⟨ var #1 , var #0 ⟩ ∷ (A ⊃ B ⊃ A ∧ B)
  E13 = MMlam MMlam ⟨ MMvar M#1 MM, MMvar M#0 ⟩
