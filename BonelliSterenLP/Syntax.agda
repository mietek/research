module BonelliSterenLP.Syntax where

open import Common.Context public
open import Common.UntypedContext public

open import Data.Nat using (_≤_ ; z≤n ; s≤s) renaming (_≟_ to _≟ₙ_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; subst)
open import Relation.Nullary using (yes ; no)


-- Proof polynomials, or term representations.

data Pf (g d : ℕ) : Set where
  `var   : Fin g → Pf g d
  `⋆var  : Fin d → Pf g d
  `lam   : Pf (suc g) d → Pf g d
  `app   : Pf g d → Pf g d → Pf g d
  `pair  : Pf g d → Pf g d → Pf g d
  `fst   : Pf g d → Pf g d
  `snd   : Pf g d → Pf g d
  `unit  : Pf g d
  `box   : Pf 0 d → Pf g d
  `unbox : Pf g d → Pf g (suc d) → Pf g d

`v₀ : ∀ {g d} → Pf (suc g) d
`v₀ = `var `i₀

`v₁ : ∀ {g d} → Pf (suc (suc g)) d
`v₁ = `var `i₁

`v₂ : ∀ {g d} → Pf (suc (suc (suc g))) d
`v₂ = `var `i₂

`⋆v₀ : ∀ {g d} → Pf g (suc d)
`⋆v₀ = `⋆var `i₀

`⋆v₁ : ∀ {g d} → Pf g (suc (suc d))
`⋆v₁ = `⋆var `i₁

`⋆v₂ : ∀ {g d} → Pf g (suc (suc (suc d)))
`⋆v₂ = `⋆var `i₂


-- Weakening.

`ren-tm : ∀ {g g′ d} → `Renᵢ g g′ → `Ren (flip Pf d) g g′
`ren-tm ρ (`var i)     = `var (ρ i)
`ren-tm ρ (`⋆var i)    = `⋆var i
`ren-tm ρ (`lam t)     = `lam (`ren-tm (`wk-renᵢ ρ) t)
`ren-tm ρ (`app t u)   = `app (`ren-tm ρ t) (`ren-tm ρ u)
`ren-tm ρ (`pair t u)  = `pair (`ren-tm ρ t) (`ren-tm ρ u)
`ren-tm ρ (`fst t)     = `fst (`ren-tm ρ t)
`ren-tm ρ (`snd t)     = `snd (`ren-tm ρ t)
`ren-tm ρ `unit        = `unit
`ren-tm ρ (`box t)     = `box t
`ren-tm ρ (`unbox t u) = `unbox (`ren-tm ρ t) (`ren-tm ρ u)

`wk-tm : ∀ {g d} → `Ren (flip Pf d) g (suc g)
`wk-tm = `ren-tm suc

`wk-tm₀ : ∀ {g d} → `Ren (flip Pf d) 0 g
`wk-tm₀ = `ren-tm (λ ())


-- Modal weakening.

`⋆ren-tm : ∀ {g d d′} → `Renᵢ d d′ → `Ren (Pf g) d d′
`⋆ren-tm ρ (`var i)     = `var i
`⋆ren-tm ρ (`⋆var i)    = `⋆var (ρ i)
`⋆ren-tm ρ (`lam t)     = `lam (`⋆ren-tm ρ t)
`⋆ren-tm ρ (`app t u)   = `app (`⋆ren-tm ρ t) (`⋆ren-tm ρ u)
`⋆ren-tm ρ (`pair t u)  = `pair (`⋆ren-tm ρ t) (`⋆ren-tm ρ u)
`⋆ren-tm ρ (`fst t)     = `fst (`⋆ren-tm ρ t)
`⋆ren-tm ρ (`snd t)     = `snd (`⋆ren-tm ρ t)
`⋆ren-tm ρ `unit        = `unit
`⋆ren-tm ρ (`box t)     = `box (`⋆ren-tm ρ t)
`⋆ren-tm ρ (`unbox t u) = `unbox (`⋆ren-tm ρ t) (`⋆ren-tm (`wk-renᵢ ρ) u)

`⋆wk-tm : ∀ {g d} → `Ren (Pf g) d (suc d)
`⋆wk-tm = `⋆ren-tm suc


-- Substitution.

`[_≔_]ᵢ_ : ∀ {g d} → (i : Fin g) → Pf (g `-ᵢ i) d → `Subᵢ (flip Pf d) g (g `-ᵢ i)
`[ i ≔ ν ]ᵢ j  with i `≟ᵢ j
`[ i ≔ ν ]ᵢ .i | same   = ν
`[ i ≔ ν ]ᵢ ._ | diff j = `var j

`[_≔_]_ : ∀ {g d} → (i : Fin g) → Pf (g `-ᵢ i) d → `Sub (flip Pf d) g (g `-ᵢ i)
`[ i ≔ ν ] (`var j)     = `[ i ≔ ν ]ᵢ j
`[ i ≔ ν ] (`⋆var j)    = `⋆var j
`[ i ≔ ν ] (`lam t)     = `lam (`[ suc i ≔ `wk-tm ν ] t)
`[ i ≔ ν ] (`app t u)   = `app (`[ i ≔ ν ] t) (`[ i ≔ ν ] u)
`[ i ≔ ν ] (`pair t u)  = `pair (`[ i ≔ ν ] t) (`[ i ≔ ν ] u)
`[ i ≔ ν ] (`fst t)     = `fst (`[ i ≔ ν ] t)
`[ i ≔ ν ] (`snd t)     = `snd (`[ i ≔ ν ] t)
`[ i ≔ ν ] `unit        = `unit
`[ i ≔ ν ] (`box t)     = `box t
`[ i ≔ ν ] (`unbox t u) = `unbox (`[ i ≔ ν ] t) (`[ i ≔ `⋆wk-tm ν ] u)


-- Modal substitution.

`⋆[_≔_]ᵢ_ : ∀ {g d} → (i : Fin d) → Pf 0 (d `-ᵢ i) → `Subᵢ (Pf g) d (d `-ᵢ i)
`⋆[ i ≔ ν ]ᵢ j  with i `≟ᵢ j
`⋆[ i ≔ ν ]ᵢ .i | same   = `wk-tm₀ ν
`⋆[ i ≔ ν ]ᵢ ._ | diff j = `⋆var j

`⋆[_≔_]_ : ∀ {g d} → (i : Fin d) → Pf 0 (d `-ᵢ i) → `Sub (Pf g) d (d `-ᵢ i)
`⋆[ i ≔ ν ] (`var j)     = `var j
`⋆[ i ≔ ν ] (`⋆var j)    = `⋆[ i ≔ ν ]ᵢ j
`⋆[ i ≔ ν ] (`lam t)     = `lam (`⋆[ i ≔ ν ] t)
`⋆[ i ≔ ν ] (`app t u)   = `app (`⋆[ i ≔ ν ] t) (`⋆[ i ≔ ν ] u)
`⋆[ i ≔ ν ] (`pair t u)  = `pair (`⋆[ i ≔ ν ] t) (`⋆[ i ≔ ν ] u)
`⋆[ i ≔ ν ] (`fst t)     = `fst (`⋆[ i ≔ ν ] t)
`⋆[ i ≔ ν ] (`snd t)     = `snd (`⋆[ i ≔ ν ] t)
`⋆[ i ≔ ν ] `unit        = `unit
`⋆[ i ≔ ν ] (`box t)     = `box (`⋆[ i ≔ ν ] t)
`⋆[ i ≔ ν ] (`unbox t u) = `unbox (`⋆[ i ≔ ν ] t) (`⋆[ suc i ≔ `⋆wk-tm ν ] u)


-- Types.

infixl 5 _∧_
infixr 3 _⊃_
data Ty : Set where
  ι    : Ty
  _⊃_  : Ty → Ty → Ty
  _∧_  : Ty → Ty → Ty
  [_]_ : ∀ {d} → Pf 0 d → Ty → Ty
  ⊤   : Ty


-- Modal weakening inside types.

⋆ren-ty : ∀ {d d′} → `Renᵢ d d′ → Ty → Ty
⋆ren-ty ρ ι         = ι
⋆ren-ty ρ (A ⊃ B)   = ⋆ren-ty ρ A ⊃ ⋆ren-ty ρ B
⋆ren-ty ρ (A ∧ B)   = ⋆ren-ty ρ A ∧ ⋆ren-ty ρ B
⋆ren-ty {d} ρ ([_]_ {d′} t A) with d ≟ₙ d′
⋆ren-ty ρ ([ t ] A) | yes refl = [ `⋆ren-tm ρ t ] (⋆ren-ty ρ A)
⋆ren-ty ρ ([ t ] A) | no  d≢d′ = [ t ] A
⋆ren-ty ρ ⊤        = ⊤

⋆wk-ty : ∀ {d} → Ty → Ty
⋆wk-ty {d} = ⋆ren-ty {d} suc

⋆ren-cx : ∀ {d d′} → `Renᵢ d d′ → Cx Ty → Cx Ty
⋆ren-cx ρ ∅       = ∅
⋆ren-cx ρ (Γ , A) = ⋆ren-cx ρ Γ , ⋆ren-ty ρ A

len-ren-cx : ∀ {d d′} → (ρ : `Renᵢ d d′) (Γ : Cx Ty) → length Γ ≡ length (⋆ren-cx ρ Γ)
len-ren-cx ρ ∅       = refl
len-ren-cx ρ (Γ , A) = cong suc (len-ren-cx ρ Γ)


-- Modal substitution inside types.

⋆[_≔_]ty_ : ∀ {d} → (i : Fin d) → Pf 0 (d `-ᵢ i) → Ty → Ty
⋆[ i ≔ ν ]ty ι         = ι
⋆[ i ≔ ν ]ty (A ⊃ B)   = (⋆[ i ≔ ν ]ty A) ⊃ (⋆[ i ≔ ν ]ty B)
⋆[ i ≔ ν ]ty (A ∧ B)   = (⋆[ i ≔ ν ]ty A) ∧ (⋆[ i ≔ ν ]ty B)
⋆[_≔_]ty_ {d} i ν ([_]_ {d′} t A) with d ≟ₙ d′
⋆[ i ≔ ν ]ty ([ t ] A) | yes refl = [ `⋆[ i ≔ ν ] t ] (⋆[ i ≔ ν ]ty A)
⋆[ i ≔ ν ]ty ([ t ] A) | no  d≢d′ = [ t ] A
⋆[ i ≔ ν ]ty ⊤        = ⊤

⋆[_≔_]cx_ : ∀ {d} → (i : Fin d) → Pf 0 (d `-ᵢ i) → Cx Ty → Cx Ty
⋆[ i ≔ ν ]cx ∅       = ∅
⋆[ i ≔ ν ]cx (Γ , A) = (⋆[ i ≔ ν ]cx Γ) , (⋆[ i ≔ ν ]ty A)


-- Terms.

data Tm (Γ Δ : Cx Ty) : Ty → Pf (length Γ) (length Δ) → Set where
  var   : ∀ {A} → (i : A ∈ Γ) → Tm Γ Δ A (`var (index i))
  ⋆var  : ∀ {A} → (i : A ∈ Δ) → Tm Γ Δ A (`⋆var (index i))
  lam   : ∀ {A B t} → Tm (Γ , A) Δ B t → Tm Γ Δ (A ⊃ B) (`lam t)
  app   : ∀ {A B t u} → Tm Γ Δ (A ⊃ B) t → Tm Γ Δ A u → Tm Γ Δ B (`app t u)
  pair  : ∀ {A B t u} → Tm Γ Δ A t → Tm Γ Δ B u → Tm Γ Δ (A ∧ B) (`pair t u)
  fst   : ∀ {A B t} → Tm Γ Δ (A ∧ B) t → Tm Γ Δ A (`fst t)
  snd   : ∀ {A B t} → Tm Γ Δ (A ∧ B) t → Tm Γ Δ B (`snd t)
  unit  : Tm Γ Δ ⊤ `unit
  box   : ∀ {A} {t : Pf 0 (length Δ)} → Tm ∅ Δ A t → Tm Γ Δ ([ t ] A) (`box t)
  unbox : ∀ {A C t u} {s : Pf 0 (length Δ)} → Tm Γ Δ ([ s ] A) t → Tm Γ (Δ , A) C u → Tm Γ Δ (⋆[ zero ≔ s ]ty C) (`unbox t u)

v₀ : ∀ {A Γ Δ} → Tm (Γ , A) Δ A (`var zero)
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → Tm (Γ , A , B) Δ A (`var (suc zero))
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → Tm (Γ , A , B , C) Δ A (`var (suc (suc zero)))
v₂ = var i₂

⋆v₀ : ∀ {A Γ Δ} → Tm Γ (Δ , A) A (`⋆var zero)
⋆v₀ = ⋆var i₀

⋆v₁ : ∀ {A B Γ Δ} → Tm Γ (Δ , A , B) A (`⋆var (suc zero))
⋆v₁ = ⋆var i₁

⋆v₂ : ∀ {A B C Γ Δ} → Tm Γ (Δ , A , B , C) A (`⋆var (suc (suc zero)))
⋆v₂ = ⋆var i₂


-- Weakening.

record 2Renᵢ (Γ Γ′ : Cx Ty) : Set where
  field
    ren  : Renᵢ Γ Γ′
    `ren : `Renᵢ (length Γ) (length Γ′)
    lem₁ : ∀ {A} → (i : A ∈ Γ) → `ren (index i) ≡ index (ren i)
open 2Renᵢ public

2wk-renᵢ : ∀ {A Γ Γ′} → 2Renᵢ Γ Γ′ → 2Renᵢ (Γ , A) (Γ′ , A)
ren  (2wk-renᵢ ρ) = wk-renᵢ (ren ρ)
`ren (2wk-renᵢ ρ) = `wk-renᵢ (`ren ρ)
lem₁ (2wk-renᵢ ρ) top     = refl
lem₁ (2wk-renᵢ ρ) (pop i) = cong suc (lem₁ ρ i)

ren-tm : ∀ {A Γ Γ′ Δ t} → (ρ : 2Renᵢ Γ Γ′) → Tm Γ Δ A t → Tm Γ′ Δ A (`ren-tm (`ren ρ) t)
ren-tm ρ (var i)     rewrite lem₁ ρ i = var (ren ρ i)
ren-tm ρ (⋆var i)    = ⋆var i
ren-tm ρ (lam t)     = lam (ren-tm (2wk-renᵢ ρ) t)
ren-tm ρ (app t u)   = app (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (pair t u)  = pair (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (fst t)     = fst (ren-tm ρ t)
ren-tm ρ (snd t)     = snd (ren-tm ρ t)
ren-tm ρ unit        = unit
ren-tm ρ (box t)     = box t
ren-tm ρ (unbox t u) = unbox (ren-tm ρ t) (ren-tm ρ u)

⋆ren-tm : ∀ {A Γ Δ Δ′ t} → (ρ : 2Renᵢ Δ Δ′) → Tm Γ Δ A t →
          Tm (⋆ren-cx (`ren ρ) Γ) Δ′
             (⋆ren-ty (`ren ρ) A)
             (subst (λ g → Pf g (length Δ′))
                    (len-ren-cx (`ren ρ) Γ)
                    (`⋆ren-tm (`ren ρ) t))
⋆ren-tm ρ (var i)     = {!var i!} -- var i
⋆ren-tm ρ (⋆var i)    rewrite lem₁ ρ i = {!!} -- ⋆var (ren ρ i)
⋆ren-tm ρ (lam t)     = {!!} -- lam {!⋆ren-tm ? t!}
⋆ren-tm ρ (app t u)   = {!app (⋆ren-tm ρ t) (⋆ren-tm ρ u)!}
⋆ren-tm ρ (pair t u)  = {!pair (⋆ren-tm ρ t) (⋆ren-tm ρ u)!}
⋆ren-tm ρ (fst t)     = {!fst (⋆ren-tm ρ t)!}
⋆ren-tm ρ (snd t)     = {!snd (⋆ren-tm ρ t)!}
⋆ren-tm ρ unit        = {!unit!}
⋆ren-tm ρ (box t)     = {!box (⋆ren-tm ρ t)!}
⋆ren-tm ρ (unbox t u) = {!unbox (⋆ren-tm ρ t) ?!}
