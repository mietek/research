{-# OPTIONS --rewriting #-}

module A201802.WIP.CurryHoward where

open import A201801.Prelude
open import A201801.Fin
open import A201801.List
open import A201801.Vec
open import A201801.VecLemmas


--------------------------------------------------------------------------------


-- Propositions as types

infixr 8 _⊃_
data Type : Set
  where
    ι   : Type
    _⊃_ : Type → Type → Type


--------------------------------------------------------------------------------


-- IPL derivations, or evidence for the judgment of truth,
-- or Church-style intrinsically typed terms
--
-- We read `Γ ⊢ A true` as:
-- Assuming `Γ` is all true, `A` is true

infix 3 _⊢_true
data _⊢_true : List Type → Type → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true

id₁ : ∀ {Γ A} → Γ ⊢ A ⊃ A true
id₁ = lam (var zero)


--------------------------------------------------------------------------------


-- STLC terms

data Term : Nat → Set
  where
    VAR : ∀ {g} → Fin g → Term g
    LAM : ∀ {g} → Term (suc g) → Term g
    APP : ∀ {g} → Term g → Term g → Term g

ID₁ : ∀ {g} → Term g
ID₁ = LAM (VAR zero)


-- STLC derivations, or evidence for the judgment of type assignment,
-- or Curry-style extrinsically typed terms
--
-- We read `Γ ⊢ M ⦂ A` as:
-- `M` represents some derivation of `A true`, in which we assume `Γ` is all true

infix 3 _⊢_⦂_
data _⊢_⦂_ : ∀ {g} → Vec Type g → Term g → Type → Set
  where
    var : ∀ {A g I} → {Γ : Vec Type g}
                    → Γ ∋⟨ I ⟩ A
                    → Γ ⊢ VAR I ⦂ A

    lam : ∀ {A B g M} → {Γ : Vec Type g}
                      → Γ , A ⊢ M ⦂ B
                      → Γ ⊢ LAM M ⦂ A ⊃ B

    app : ∀ {A B g M N} → {Γ : Vec Type g}
                        → Γ ⊢ M ⦂ A ⊃ B → Γ ⊢ N ⦂ A
                        → Γ ⊢ APP M N ⦂ B


--------------------------------------------------------------------------------


-- Evidence for a helper judgment
--
-- We read `Γ ⊢ M ⦂ A ⟺ 𝒟` as:
-- `M` represents the derivation `𝒟` of `A true`, in which we assume `Γ` is all true

infix 3 _⊢_⦂_⟺_
data _⊢_⦂_⟺_ : ∀ {g} → (Γ : List Type) → Term g → (A : Type)
                        → Γ ⊢ A true → Set
  where
    var : ∀ {A g Γ i} → (I : Fin g)
                      → Γ ⊢ VAR (toFin i) ⦂ A ⟺ var i

    lam : ∀ {A B g Γ 𝒟} → {M : Term (suc g)}
                        → Γ , A ⊢ M ⦂ B ⟺ 𝒟
                        → Γ ⊢ LAM M ⦂ A ⊃ B ⟺ lam 𝒟

    app : ∀ {A B g Γ 𝒟 ℰ} → {M N : Term g}
                          → Γ ⊢ M ⦂ A ⊃ B ⟺ 𝒟 → Γ ⊢ N ⦂ A ⟺ ℰ
                          → Γ ⊢ APP M N ⦂ B ⟺ app 𝒟 ℰ


--------------------------------------------------------------------------------


-- Forgetful projection from IPL derivations to STLC terms

° : ∀ {Γ A} → Γ ⊢ A true
            → Term (len Γ)
° (var i)   = VAR (toFin i)
° (lam 𝒟)   = LAM (° 𝒟)
° (app 𝒟 ℰ) = APP (° 𝒟) (° ℰ)


-- ° upholds equivalence

lem° : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
               → Γ ⊢ ° 𝒟 ⦂ A ⟺ 𝒟
lem° (var i)   = var (toFin i)
lem° (lam 𝒟)   = lam (lem° 𝒟)
lem° (app 𝒟 ℰ) = app (lem° 𝒟) (lem° ℰ)

-- hm : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
--              → Σ (Term (len Γ)) (\ M → Γ ⊢ M ⦂ A ⟺ 𝒟)
-- hm (var i)   = VAR (toFin i) , var {!!}
-- hm (lam 𝒟)   = {!!}
-- hm (app 𝒟 ℰ) = {!!}


--------------------------------------------------------------------------------


-- Mapping from IPL derivations to STLC derivations

↓ : ∀ {Γ M A} → (𝒟 : Γ ⊢ A true) → Γ ⊢ M ⦂ A ⟺ 𝒟
              → fromList Γ ⊢ M ⦂ A
↓ (var i)   (var I)   = var (from∋ i)
↓ (lam 𝒟)   (lam p)   = lam (↓ 𝒟 p)
↓ (app 𝒟 ℰ) (app p q) = app (↓ 𝒟 p) (↓ ℰ q)


-- Mapping from STLC derivations to IPL derivations

↑ : ∀ {g M A} → {Γ : Vec Type g}
              → Γ ⊢ M ⦂ A
              → toList Γ ⊢ A true
↑ (var i)   = var (to∋ i)
↑ (lam 𝒟)   = lam (↑ 𝒟)
↑ (app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


-- ↑ upholds equivalence

-- TODO: broken
-- lem↑ : ∀ {g M A} → {Γ : Vec Type g}
--                  → (𝒟 : Γ ⊢ M ⦂ A)
--                  → toList Γ ⊢ M ⦂ A ⟺ ↑ 𝒟
-- lem↑ (var {I = I} i) = {!var I!}
-- lem↑ (lam 𝒟)         = lam (lem↑ 𝒟)
-- lem↑ (app 𝒟 ℰ)       = app (lem↑ 𝒟) (lem↑ ℰ)


--------------------------------------------------------------------------------


gid↑↓ : ∀ {Γ M A} → (𝒟 : Γ ⊢ A true) (p : Γ ⊢ M ⦂ A ⟺ 𝒟)
                  → ↑ (↓ 𝒟 p) ≡ 𝒟
gid↑↓ (var i)   (var I)   = refl
gid↑↓ (lam 𝒟)   (lam p)   = lam & gid↑↓ 𝒟 p
gid↑↓ (app 𝒟 ℰ) (app p q) = app & gid↑↓ 𝒟 p ⊗ gid↑↓ ℰ q


gid↓↑ : ∀ {g M A} → {Γ : Vec Type g}
                  → (𝒟 : Γ ⊢ M ⦂ A) (p : toList Γ ⊢ M ⦂ A ⟺ ↑ 𝒟)
                  → ↓ (↑ 𝒟) p ≡ 𝒟
gid↓↑ (var i)   (var I)   = refl
gid↓↑ (lam 𝒟)   (lam p)   = lam & gid↓↑ 𝒟 p
gid↓↑ (app 𝒟 ℰ) (app p q) = app & gid↓↑ 𝒟 p ⊗ gid↓↑ ℰ q


--------------------------------------------------------------------------------


-- TODO: broken
-- id↑↓ : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
--                → {!↑ (↓ 𝒟)!} ≡ 𝒟
-- id↑↓ 𝒟 = gid↑↓ 𝒟 (lem° 𝒟)
--
--
-- id↓↑ : ∀ {g M A} → {Γ : Vec Type g}
--                  → (𝒟 : Γ ⊢ M ⦂ A)
--                  → {!↓ (↑ 𝒟)!} ≡ 𝒟
-- id↓↑ 𝒟 = gid↓↑ 𝒟 (lem↑ 𝒟)


--------------------------------------------------------------------------------
