{-# OPTIONS --allow-unsolved-metas #-}

{-

An extension of reflective λ-calculus
=====================================

A work-in-progress implementation of the Alt-Artëmov system λ∞,
extended with disjunction and falsehood.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") (":." "∵")
     ("v" "𝑣")
     ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("l4" "𝜆⁴") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("o4" "∘⁴") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("p4" "𝑝⁴") ("pn" "𝑝ⁿ")
     ("pi" "𝜋")
     ("pi0" "𝜋₀") ("pi02" "𝜋₀²") ("pi03" "𝜋₀³") ("pi04" "𝜋₀⁴") ("pi0n" "𝜋₀ⁿ")
     ("pi1" "𝜋₁") ("pi12" "𝜋₁²") ("pi13" "𝜋₁³") ("pi14" "𝜋₁⁴") ("pi1n" "𝜋₁ⁿ")
     ("io" "𝜄")
     ("io0" "𝜄₀") ("io02" "𝜄₀²") ("io03" "𝜄₀³") ("io04" "𝜄₀⁴") ("io0n" "𝜄₀ⁿ")
     ("io1" "𝜄₁") ("io12" "𝜄₁²") ("io13" "𝜄₁³") ("io14" "𝜄₁⁴") ("io1n" "𝜄₁ⁿ")
     ("c" "𝑐") ("c2" "𝑐²") ("c3" "𝑐³") ("c4" "𝑐⁴") ("cn" "𝑐ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("u4" "⇑⁴") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("d4" "⇓⁴") ("dn" "⇓ⁿ")
     ("x" "☆") ("x2" "☆²") ("x3" "☆³") ("x4" "☆⁴") ("xn" "☆ⁿ")
     ("b" "□")
     ("mv" "𝒗")
     ("ml" "𝝀") ("ml2" "𝝀²") ("ml3" "𝝀³") ("ml4" "𝝀⁴") ("mln" "𝝀ⁿ")
     ("mo" "∙") ("mo2" "∙²") ("mo3" "∙³") ("mo4" "∙⁴") ("mon" "∙ⁿ")
     ("mp" "𝒑") ("mp2" "𝒑²") ("mp3" "𝒑³") ("mp4" "𝒑⁴") ("mpn" "𝒑ⁿ")
     ("mpi" "𝝅")
     ("mpi0" "𝝅₀") ("mpi02" "𝝅₀²") ("mpi03" "𝝅₀³") ("mpi04" "𝝅₀⁴") ("mpi0n" "𝝅₀ⁿ")
     ("mpi1" "𝝅₁") ("mpi12" "𝝅₁²") ("mpi13" "𝝅₁³") ("mpi14" "𝝅₁⁴") ("mpi1n" "𝝅₁ⁿ")
     ("mi" "𝜾")
     ("mi0" "𝜾₀") ("mi02" "𝜾₀²") ("mi03" "𝜾₀³") ("mi04" "𝜾₀⁴") ("mi0n" "𝜾₀ⁿ")
     ("mi1" "𝜾₁") ("mi12" "𝜾₁²") ("mi13" "𝜾₁³") ("mi14" "𝜾₁⁴") ("mi1n" "𝜾₁ⁿ")
     ("mc" "𝒄") ("mc2" "𝒄²") ("mc3" "𝒄³") ("mc4" "𝒄⁴") ("mcn" "𝒄ⁿ")
     ("mu" "⬆") ("mu2" "⬆²") ("mu3" "⬆³") ("mu4" "⬆⁴") ("mun" "⬆ⁿ")
     ("md" "⬇") ("md2" "⬇²") ("md3" "⬇³") ("md4" "⬇⁴") ("mdn" "⬇ⁿ")
     ("mx" "★") ("mx2" "★²") ("mx3" "★³") ("mx4" "★⁴") ("mxn" "★ⁿ")
     ("mb" "■")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("ss" "𝐬") ("ts" "𝐭") ("us" "𝐮") ("xs" "𝐱") ("ys" "𝐲") ("zs" "𝐳")
     ("C" "𝒞") ("D" "𝒟") ("E" "ℰ") ("F" "ℱ") ("I" "ℐ") ("X" "𝒳")
     ("N" "ℕ"))))

-}


module A201602.AltArtemov-WIP2 where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_)


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Variables
Var : Set
Var = ℕ


-- Term constructors
data Tm : Set where
  -- Variable reference
  𝑣[_]_ : ℕ → Var → Tm

  -- Abstraction (⊃I) at level n
  𝜆[_]_ : ℕ → Tm → Tm

  -- Application (⊃E) at level n
  _∘[_]_ : Tm → ℕ → Tm → Tm

  -- Pair (∧I) at level n
  𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm

  -- 0th projection (∧E₀) at level n
  𝜋₀[_]_ : ℕ → Tm → Tm

  -- 1st projection (∧E₁) at level n
  𝜋₁[_]_ : ℕ → Tm → Tm

  -- 0th injection (∨I₀) at level n
  𝜄₀[_]_ : ℕ → Tm → Tm

  -- 1st injection (∨I₁) at level n
  𝜄₁[_]_ : ℕ → Tm → Tm

  -- Case split (∨E) at level n
  𝑐[_][_▷_∣_] : ℕ → Tm → Tm → Tm → Tm

  -- Artëmov’s “proof checker”
  !_ : Tm → Tm

  -- Reification at level n
  ⇑[_]_ : ℕ → Tm → Tm

  -- Reflection at level n
  ⇓[_]_ : ℕ → Tm → Tm

  -- Explosion (⊥E) at level n
  ☆[_]_ : ℕ → Tm → Tm


-- Type constructors
infixr 5 _∶_
infixl 4 _∧_
infixl 3 _∨_
infixr 2 _⊃_
data Ty : Set where
  -- Implication
  _⊃_ : Ty → Ty → Ty

  -- Conjunction
  _∧_ : Ty → Ty → Ty

  -- Disjunction
  _∨_ : Ty → Ty → Ty

  -- Explicit provability
  _∶_ : Tm → Ty → Ty

  -- Falsehood
  ⊥ : Ty


-- --------------------------------------------------------------------------
--
-- Example types


-- Truth
⊤ : Ty
⊤ = ⊥ ⊃ ⊥

-- Negation
infixr 4 ¬_
¬_ : Ty → Ty
¬ A = A ⊃ ⊥

-- Equivalence
infixr 1 _⫗_
_⫗_ : Ty → Ty → Ty
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 1


𝑣_ : Var → Tm
𝑣 i = 𝑣[ 1 ] i

infixr 5 𝜆_
𝜆_ : Tm → Tm
𝜆 t = 𝜆[ 1 ] t

infixl 7 _∘_
_∘_ : Tm → Tm → Tm
t ∘ s = t ∘[ 1 ] s

𝑝⟨_,_⟩ : Tm → Tm → Tm
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝜋₀_ : Tm → Tm
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₁_ : Tm → Tm
𝜋₁ t = 𝜋₁[ 1 ] t

𝜄₀_ : Tm → Tm
𝜄₀ t = 𝜄₀[ 1 ] t

𝜄₁_ : Tm → Tm
𝜄₁ t = 𝜄₁[ 1 ] t

𝑐[_▷_∣_] : Tm → Tm → Tm → Tm
𝑐[ t ▷ s ∣ r ] = 𝑐[ 1 ][ t ▷ s ∣ r ]

⇑_ : Tm → Tm
⇑ t = ⇑[ 1 ] t

⇓_ : Tm → Tm
⇓ t = ⇓[ 1 ] t

☆_ : Tm → Tm
☆ t = ☆[ 1 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 2


𝑣² : Var → Tm
𝑣² i₂ = 𝑣[ 2 ] i₂

infixr 5 𝜆²_
𝜆²_ : Tm → Tm
𝜆² t₂ = 𝜆[ 2 ] t₂

infixl 7 _∘²_
_∘²_ : Tm → Tm → Tm
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝²⟨_,_⟩ : Tm → Tm → Tm
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀²_ : Tm → Tm
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁²_ : Tm → Tm
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

𝜄₀²_ : Tm → Tm
𝜄₀² t₂ = 𝜄₀[ 2 ] t₂

𝜄₁²_ : Tm → Tm
𝜄₁² t₂ = 𝜄₁[ 2 ] t₂

𝑐²[_▷_∣_] : Tm → Tm → Tm → Tm
𝑐²[ t₂ ▷ s₂ ∣ r₂ ] = 𝑐[ 2 ][ t₂ ▷ s₂ ∣ r₂ ]

⇑²_ : Tm → Tm
⇑² t₂ = ⇑[ 2 ] t₂

⇓²_ : Tm → Tm
⇓² t₂ = ⇓[ 2 ] t₂

☆²_ : Tm → Tm
☆² t = ☆[ 2 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 3


𝑣³_ : Var → Tm
𝑣³ i₃ = 𝑣[ 3 ] i₃

infixr 5 𝜆³_
𝜆³_ : Tm → Tm
𝜆³ t₃ = 𝜆[ 3 ] t₃

infixl 7 _∘³_
_∘³_ : Tm → Tm → Tm
t₃ ∘³ s₃ = t₃ ∘[ 3 ] s₃

𝑝³⟨_,_⟩ : Tm → Tm → Tm
𝑝³⟨ t₃ , s₃ ⟩ = 𝑝[ 3 ]⟨ t₃ , s₃ ⟩

𝜋₀³_ : Tm → Tm
𝜋₀³ t₃ = 𝜋₀[ 3 ] t₃

𝜋₁³_ : Tm → Tm
𝜋₁³ t₃ = 𝜋₁[ 3 ] t₃

𝜄₀³_ : Tm → Tm
𝜄₀³ t₃ = 𝜄₀[ 3 ] t₃

𝜄₁³_ : Tm → Tm
𝜄₁³ t₃ = 𝜄₁[ 3 ] t₃

𝑐³[_▷_∣_] : Tm → Tm → Tm → Tm
𝑐³[ t₃ ▷ s₃ ∣ r₃ ] = 𝑐[ 3 ][ t₃ ▷ s₃ ∣ r₃ ]

⇑³_ : Tm → Tm
⇑³ t₃ = ⇑[ 3 ] t₃

⇓³_ : Tm → Tm
⇓³ t₃ = ⇓[ 3 ] t₃

☆³_ : Tm → Tm
☆³ t = ☆[ 3 ] t


-- --------------------------------------------------------------------------
--
-- Notation for term constructors at level 4


𝑣⁴_ : Var → Tm
𝑣⁴ i₄ = 𝑣[ 4 ] i₄

infixr 5 𝜆⁴_
𝜆⁴_ : Tm → Tm
𝜆⁴ t₄ = 𝜆[ 4 ] t₄

infixl 7 _∘⁴_
_∘⁴_ : Tm → Tm → Tm
t₄ ∘⁴ s₄ = t₄ ∘[ 4 ] s₄

𝑝⁴⟨_,_⟩ : Tm → Tm → Tm
𝑝⁴⟨ t₄ , s₄ ⟩ = 𝑝[ 4 ]⟨ t₄ , s₄ ⟩

𝜋₀⁴_ : Tm → Tm
𝜋₀⁴ t₄ = 𝜋₀[ 4 ] t₄

𝜋₁⁴_ : Tm → Tm
𝜋₁⁴ t₄ = 𝜋₁[ 4 ] t₄

𝜄₀⁴_ : Tm → Tm
𝜄₀⁴ t₄ = 𝜄₀[ 4 ] t₄

𝜄₁⁴_ : Tm → Tm
𝜄₁⁴ t₄ = 𝜄₁[ 4 ] t₄

𝑐⁴[_▷_∣_] : Tm → Tm → Tm → Tm
𝑐⁴[ t₄ ▷ s₄ ∣ r₄ ] = 𝑐[ 4 ][ t₄ ▷ s₄ ∣ r₄ ]

⇑⁴_ : Tm → Tm
⇑⁴ t₄ = ⇑[ 4 ] t₄

⇓⁴_ : Tm → Tm
⇓⁴ t₄ = ⇓[ 4 ] t₄

☆⁴_ : Tm → Tm
☆⁴ t = ☆[ 4 ] t


-- --------------------------------------------------------------------------
--
-- Vector notation for type assertions at level n (p. 27 [1])


map# : ∀{n} {X Y : Set}
    → (ℕ → X → Y) → Vec X n → Vec Y n
map# {zero}  f []      = []
map# {suc n} f (x ∷ 𝐱) = f (suc n) x ∷ map# f 𝐱

map2# : ∀{n} {X Y Z : Set}
    → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
map2# {zero}  f []      []      = []
map2# {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) = f (suc n) x y ∷ map2# f 𝐱 𝐲

map3# : ∀{n} {X Y Z A : Set}
    → (ℕ → X → Y → Z → A) → Vec X n → Vec Y n → Vec Z n → Vec A n
map3# {zero}  f []      []      []      = []
map3# {suc n} f (x ∷ 𝐱) (y ∷ 𝐲) (z ∷ 𝐳) = f (suc n) x y z ∷ map3# f 𝐱 𝐲 𝐳


-- Term vectors
Vars : ℕ → Set
Vars = Vec Var

Tms : ℕ → Set
Tms = Vec Tm


-- tₙ ∶ tₙ₋₁ ∶ … ∶ t ∶ A
infixr 5 _∵_
_∵_ : ∀{n} → Tms n → Ty → Ty
[]      ∵ A = A
(x ∷ 𝐭) ∵ A = x ∶ 𝐭 ∵ A

-- 𝑣 x ∶ 𝑣 x ∶ … ∶ 𝑣 x
𝑣ⁿ_ : ∀{n} → Vars n → Tms n
𝑣ⁿ_ = map# 𝑣[_]_

-- 𝜆ⁿ tₙ ∶ 𝜆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜆 t
infixr 5 𝜆ⁿ_
𝜆ⁿ_ : ∀{n} → Tms n → Tms n
𝜆ⁿ_ = map# 𝜆[_]_

-- tₙ ∘ⁿ sₙ ∶ tₙ₋₁ ∘ⁿ⁻¹ ∶ sₙ₋₁ ∶ … ∶ t ∘ s
infixl 7 _∘ⁿ_
_∘ⁿ_ : ∀{n} → Tms n → Tms n → Tms n
_∘ⁿ_ = map2# (λ n t s → t ∘[ n ] s)

-- 𝑝ⁿ⟨ tₙ , sₙ ⟩ ∶ 𝑝ⁿ⁻¹⟨ tₙ₋₁ , sₙ₋₁ ⟩ ∶ … ∶ p⟨ t , s ⟩
𝑝ⁿ⟨_,_⟩ : ∀{n} → Tms n → Tms n → Tms n
𝑝ⁿ⟨_,_⟩ = map2# 𝑝[_]⟨_,_⟩

-- 𝜋₀ⁿ tₙ ∶ 𝜋₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₀ t
𝜋₀ⁿ_ : ∀{n} → Tms n → Tms n
𝜋₀ⁿ_ = map# 𝜋₀[_]_

-- 𝜋₁ⁿ tₙ ∶ 𝜋₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₁ t
𝜋₁ⁿ_ : ∀{n} → Tms n → Tms n
𝜋₁ⁿ_ = map# 𝜋₁[_]_

-- 𝜄₀ⁿ tₙ ∶ 𝜄₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₀ t
𝜄₀ⁿ_ : ∀{n} → Tms n → Tms n
𝜄₀ⁿ_ = map# 𝜄₀[_]_

-- 𝜄₁ⁿ tₙ ∶ 𝜄₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₁ t
𝜄₁ⁿ_ : ∀{n} → Tms n → Tms n
𝜄₁ⁿ_ = map# 𝜄₁[_]_

-- 𝑐ⁿ[ tₙ ▷ sₙ ∣ rₙ ] ∶ 𝑐ⁿ⁻¹[ tₙ₋₁ ▷ sₙ₋₁ ∣ rₙ₋₁ ] ∶ … ∶ 𝑐[ t ▷ s ∣ r ]
𝑐ⁿ[_▷_∣_] : ∀{n} → Tms n → Tms n → Tms n → Tms n
𝑐ⁿ[_▷_∣_] = map3# 𝑐[_][_▷_∣_]

-- ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇑ⁿ_ : ∀{n} → Tms n → Tms n
⇑ⁿ_ = map# ⇑[_]_

-- ⇓ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇓ⁿ_ : ∀{n} → Tms n → Tms n
⇓ⁿ_ = map# ⇓[_]_

-- ☆ⁿ tₙ ∶ ☆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ☆ t
☆ⁿ_ : ∀{n} → Tms n → Tms n
☆ⁿ_ = map# ☆[_]_


-- --------------------------------------------------------------------------
--
-- Typed syntax


-- Contexts
infixl 3 _,_
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx


infixl 3 _„_
_„_ : Cx → Cx → Cx
Γ „ ∅       = Γ
Γ „ (Δ , A) = Γ „ Δ , A


-- Context membership evidence
data _∈_ : Ty → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈ (Γ , A)

  𝐒_ : ∀{A B Γ}
      → A ∈ Γ
      → A ∈ (Γ , B)


-- Forgetful projection of context membership evidence
ix : ∀{A Γ} → A ∈ Γ → ℕ
ix 𝐙     = zero
ix (𝐒 i) = suc (ix i)


-- Typed terms
infixl 7 _∙ⁿ_
infixr 5 𝝀ⁿ_
infixr 0 _⊢_
data _⊢_ (Γ : Cx) : Ty → Set where
  -- Variable reference
  𝒗[_]_ : ∀{A} (n : ℕ)
      → (𝒟 : A ∈ Γ)
      → Γ ⊢ 𝑣ⁿ (replicate n (ix 𝒟)) ∵ A

  -- Abstraction (⊃I) at level n
  𝝀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ , A ⊢ 𝐭 ∵ B
      → Γ ⊢ {!𝜆ⁿ 𝐭 ∵ (A ⊃ B)!}

  -- Application (⊃E) at level n
  _∙ⁿ_ : ∀{n} {𝐭 𝐬 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ (A ⊃ B)    → Γ ⊢ 𝐬 ∵ A
      → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∵ B

  -- Pair (∧I) at level n
  𝒑ⁿ⟨_,_⟩ : ∀{n} {𝐭 𝐬 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ A          → Γ ⊢ 𝐬 ∵ B
      → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩ ∵ (A ∧ B)

  -- 0th projection (∧E₀) at level n
  𝝅₀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ (A ∧ B)
      → Γ ⊢ 𝜋₀ⁿ 𝐭 ∵ A

  -- 1st projection (∧E₁) at level n
  𝝅₁ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ (A ∧ B)
      → Γ ⊢ 𝜋₁ⁿ 𝐭 ∵ B

  -- 0th injection (∨I₀) at level n
  𝜾₀ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ A
      → Γ ⊢ 𝜄₀ⁿ 𝐭 ∵ (A ∨ B)

  -- 1st injection (∨I₁) at level n
  𝜾₁ⁿ_ : ∀{n} {𝐭 : Tms n} {A B}
      → Γ ⊢ 𝐭 ∵ B
      → Γ ⊢ 𝜄₁ⁿ 𝐭 ∵ (A ∨ B)

  -- Case split (∨E) at level n
  𝒄ⁿ[_▷_∣_] : ∀{n} {𝐭 𝐬 𝐮 : Tms n} {A B C}
      → Γ ⊢ 𝐭 ∵ (A ∨ B)    → Γ , A ⊢ 𝐬 ∵ C
                             → Γ , B ⊢ 𝐮 ∵ C
      → Γ ⊢ 𝑐ⁿ[ 𝐭 ▷ 𝐬 ∣ 𝐮 ] ∵ C

  -- Reification at level n
  ⬆ⁿ_ : ∀{n} {𝐭 : Tms n} {u A}
      → Γ ⊢ 𝐭 ∵ (u ∶ A)
      → Γ ⊢ ⇑ⁿ 𝐭 ∵ (! u ∶ u ∶ A)

  -- Reflection at level n
  ⬇ⁿ_ : ∀{n} {𝐭 : Tms n} {u A}
      → Γ ⊢ 𝐭 ∵ (u ∶ A)
      → Γ ⊢ ⇓ⁿ 𝐭 ∵ A

  -- Explosion (⊥E)
  ★ⁿ_ : ∀{n} {𝐭 : Tms n} {A}
      → Γ ⊢ 𝐭 ∵ ⊥
      → Γ ⊢ ☆ⁿ 𝐭 ∵ A


-- Theorems
infixr 0 ⊩_
⊩_  : Ty → Set
⊩ A = ∀{Γ} → Γ ⊢ A


-- --------------------------------------------------------------------------
--
-- Notation for context membership evidence


𝟎 : ∀{A Γ}
    → A ∈ (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{A B Γ}
    → A ∈ (Γ , A , B)
𝟏 = 𝐒 𝟎

𝟐 : ∀{A B C Γ}
    → A ∈ (Γ , A , B , C)
𝟐 = 𝐒 𝟏

𝟑 : ∀{A B C D Γ}
    → A ∈ (Γ , A , B , C , D)
𝟑 = 𝐒 𝟐

𝟒 : ∀{A B C D E Γ}
    → A ∈ (Γ , A , B , C , D , E)
𝟒 = 𝐒 𝟑


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 1


𝒗_ : ∀{A Γ}
    → A ∈ Γ
    → Γ ⊢ A
𝒗 i = 𝒗[ 0 ] i

infixr 5 𝝀_
𝝀_ : ∀{A B Γ}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
𝝀_ = 𝝀ⁿ_ {𝐭 = []}

infixl 7 _∙_
_∙_ : ∀{A B Γ}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
_∙_ = _∙ⁿ_ {𝐭 = []} {𝐬 = []}

𝒑⟨_,_⟩ : ∀{A B Γ}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
𝒑⟨_,_⟩ = 𝒑ⁿ⟨_,_⟩ {𝐭 = []} {𝐬 = []}

𝝅₀_ : ∀{A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
𝝅₀_ = 𝝅₀ⁿ_ {𝐭 = []}

𝝅₁_ : ∀{A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
𝝅₁_ = 𝝅₁ⁿ_ {𝐭 = []}

𝜾₀_ : ∀{A B Γ}
    → Γ ⊢ A
    → Γ ⊢ A ∨ B
𝜾₀_ = 𝜾₀ⁿ_ {𝐭 = []}

𝜾₁_ : ∀{A B Γ}
    → Γ ⊢ B
    → Γ ⊢ A ∨ B
𝜾₁_ = 𝜾₁ⁿ_ {𝐭 = []}

𝒄[_▷_∣_] : ∀{A B C Γ}
    → Γ ⊢ A ∨ B    → Γ , A ⊢ C
                     → Γ , B ⊢ C
    → Γ ⊢ C
𝒄[_▷_∣_] = 𝒄ⁿ[_▷_∣_] {𝐭 = []} {𝐬 = []}
                              {𝐮 = []}

⬆_ : ∀{u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
⬆_ = ⬆ⁿ_ {𝐭 = []}

⬇_ : ∀{u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
⬇_ = ⬇ⁿ_ {𝐭 = []}

★_ : ∀{A Γ}
    → Γ ⊢ ⊥
    → Γ ⊢ A
★_ = ★ⁿ_ {𝐭 = []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 2


𝒗²_ : ∀{A Γ}
    → (𝒟 : A ∈ Γ)
    → Γ ⊢ 𝑣 (ix 𝒟) ∶ A
𝒗²_ i = 𝒗[ 1 ] i

infixr 5 𝝀²_
𝝀²_ : ∀{t A B Γ}
    → Γ , A ⊢ t ∶ B
    → Γ ⊢ {!𝜆 t ∶ (A ⊃ B)!}
𝝀²_ {t} =
    𝝀ⁿ_ {𝐭 = t ∷ []}

infixl 7 _∙²_
_∙²_ : ∀{t s A B Γ}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ t ∘ s ∶ B
_∙²_ {t} {s} =
    _∙ⁿ_ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝒑²⟨_,_⟩ : ∀{t s A B Γ}
    → Γ ⊢ t ∶ A          → Γ ⊢ s ∶ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑²⟨_,_⟩ {t} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t ∷ []} {𝐬 = s ∷ []}

𝝅₀²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
𝝅₀²_ {t} =
    𝝅₀ⁿ_ {𝐭 = t ∷ []}

𝝅₁²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
𝝅₁²_ {t} =
    𝝅₁ⁿ_ {𝐭 = t ∷ []}

𝜾₀²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ A
    → Γ ⊢ 𝜄₀ t ∶ (A ∨ B)
𝜾₀²_ {t} =
    𝜾₀ⁿ_ {𝐭 = t ∷ []}

𝜾₁²_ : ∀{t A B Γ}
    → Γ ⊢ t ∶ B
    → Γ ⊢ 𝜄₁ t ∶ (A ∨ B)
𝜾₁²_ {t} =
    𝜾₁ⁿ_ {𝐭 = t ∷ []}

𝒄²[_▷_∣_] : ∀{t s u A B C Γ}
    → Γ ⊢ t ∶ (A ∨ B)    → Γ , A ⊢ s ∶ C
                           → Γ , B ⊢ u ∶ C
    → Γ ⊢ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄²[_▷_∣_] {t} {s} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t ∷ []} {𝐬 = s ∷ []}
                           {𝐮 = u ∷ []}

⬆²_ : ∀{t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
⬆²_ {t} =
    ⬆ⁿ_ {𝐭 = t ∷ []}

⬇²_ : ∀{t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ ⇓ t ∶ A
⬇²_ {t} =
    ⬇ⁿ_ {𝐭 = t ∷ []}

★²_ : ∀{t A Γ}
    → Γ ⊢ t ∶ ⊥
    → Γ ⊢ ☆ t ∶ A
★²_ {t} =
    ★ⁿ_ {𝐭 = t ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 3


𝒗³_ : ∀{A Γ}
    → (𝒟 : A ∈ Γ)
    → Γ ⊢ 𝑣² (ix 𝒟) ∶ 𝑣 (ix 𝒟) ∶ A
𝒗³ i = 𝒗[ 2 ] i

infixr 5 𝝀³_
𝝀³_ : ∀{t₂ t A B Γ}
    → Γ , A ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ {!𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)!}
𝝀³_ {t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

infixl 7 _∙³_
_∙³_ : ∀{t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t ∘ s ∶ B
_∙³_ {t₂} {t} {s₂} {s} =
    _∙ⁿ_ {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}

𝒑³⟨_,_⟩ : ∀{t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ A          → Γ ⊢ s₂ ∶ s ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑³⟨_,_⟩ {t₂} {t} {s₂} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}

𝝅₀³_ : ∀{t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t ∶ A
𝝅₀³_ {t₂} {t} =
    𝝅₀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝝅₁³_ : ∀{t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t ∶ B
𝝅₁³_ {t₂} {t} =
    𝝅₁ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝜾₀³_ : ∀{t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ A
    → Γ ⊢ 𝜄₀² t₂ ∶ 𝜄₀ t ∶ (A ∨ B)
𝜾₀³_ {t₂} {t} =
    𝜾₀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝜾₁³_ : ∀{t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ 𝜄₁² t₂ ∶ 𝜄₁ t ∶ (A ∨ B)
𝜾₁³_ {t₂} {t} =
    𝜾₁ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

𝒄³[_▷_∣_] : ∀{t₂ t s₂ s u₂ u A B C Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ∨ B)    → Γ , A ⊢ s₂ ∶ s ∶ C
                                → Γ , B ⊢ u₂ ∶ u ∶ C
    → Γ ⊢ 𝑐²[ t₂ ▷ s₂ ∣ u₂ ] ∶ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄³[_▷_∣_] {t₂} {t} {s₂} {s} {u₂} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t₂ ∷ t ∷ []} {𝐬 = s₂ ∷ s ∷ []}
                                {𝐮 = u₂ ∷ u ∷ []}

⬆³_ : ∀{t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t ∶ ! u ∶ u ∶ A
⬆³_ {t₂} {t} =
    ⬆ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

⬇³_ : ∀{t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t ∶ A
⬇³_ {t₂} {t} =
    ⬇ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

★³_ : ∀{t₂ t A Γ}
    → Γ ⊢ t₂ ∶ t ∶ ⊥
    → Γ ⊢ ☆² t₂ ∶ ☆ t ∶ A
★³_ {t₂} {t} =
    ★ⁿ_ {𝐭 = t₂ ∷ t ∷ []}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 4


𝒗⁴_ : ∀{A Γ}
    → (𝒟 : A ∈ Γ)
    → Γ ⊢ 𝑣³ (ix 𝒟) ∶ 𝑣² (ix 𝒟) ∶ 𝑣 (ix 𝒟) ∶ A
𝒗⁴ i = 𝒗[ 3 ] i

infixr 5 𝝀⁴_
𝝀⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ , A ⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ ⊢ {!𝜆³ t₃ ∶ 𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)!}
𝝀⁴_ {t₃} {t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

infixl 7 _∙⁴_
_∙⁴_ : ∀{t₃ t₂ t s₃ s₂ s A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₃ ∶ s₂ ∶ s ∶ A
    → Γ ⊢ t₃ ∘³ s₃ ∶ t₂ ∘² s₂ ∶ t ∘ s ∶ B
_∙⁴_ {t₃} {t₂} {t} {s₃} {s₂} {s} =
    _∙ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}

𝒑⁴⟨_,_⟩ : ∀{t₃ t₂ t s₃ s₂ s A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ A          → Γ ⊢ s₃ ∶ s₂ ∶ s ∶ B
    → Γ ⊢ 𝑝³⟨ t₃ , s₃ ⟩ ∶ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
𝒑⁴⟨_,_⟩ {t₃} {t₂} {t} {s₃} {s₂} {s} =
    𝒑ⁿ⟨_,_⟩ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}

𝝅₀⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀³ t₃ ∶ 𝜋₀² t₂ ∶ 𝜋₀ t ∶ A
𝝅₀⁴_ {t₃} {t₂} {t} =
    𝝅₀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝝅₁⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁³ t₃ ∶ 𝜋₁² t₂ ∶ 𝜋₁ t ∶ B
𝝅₁⁴_ {t₃} {t₂} {t} =
    𝝅₁ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝜾₀⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ A
    → Γ ⊢ 𝜄₀³ t₃ ∶ 𝜄₀² t₂ ∶ 𝜄₀ t ∶ (A ∨ B)
𝜾₀⁴_ {t₃} {t₂} {t} =
    𝜾₀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝜾₁⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ ⊢ 𝜄₁³ t₃ ∶ 𝜄₁² t₂ ∶ 𝜄₁ t ∶ (A ∨ B)
𝜾₁⁴_ {t₃} {t₂} {t} =
    𝜾₁ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

𝒄⁴[_▷_∣_] : ∀{t₃ t₂ t s₃ s₂ s u₃ u₂ u A B C Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ∨ B)    → Γ , A ⊢ s₃ ∶ s₂ ∶ s ∶ C
                                     → Γ , B ⊢ u₃ ∶ u₂ ∶ u ∶ C
    → Γ ⊢ 𝑐³[ t₃ ▷ s₃ ∣ u₃ ] ∶ 𝑐²[ t₂ ▷ s₂ ∣ u₂ ] ∶ 𝑐[ t ▷ s ∣ u ] ∶ C
𝒄⁴[_▷_∣_] {t₃} {t₂} {t} {s₃} {s₂} {s} {u₃} {u₂} {u} =
    𝒄ⁿ[_▷_∣_] {𝐭 = t₃ ∷ t₂ ∷ t ∷ []} {𝐬 = s₃ ∷ s₂ ∷ s ∷ []}
                                     {𝐮 = u₃ ∷ u₂ ∷ u ∷ []}

⬆⁴_ : ∀{t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ ⇑³ t₃ ∶ ⇑² t₂ ∶ ⇑ t ∶ ! u ∶ u ∶ A
⬆⁴_ {t₃} {t₂} {t} =
    ⬆ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

⬇⁴_ : ∀{t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ ⇓³ t₃ ∶ ⇓² t₂ ∶ ⇓ t ∶ A
⬇⁴_ {t₃} {t₂} {t} =
    ⬇ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

★⁴_ : ∀{t₃ t₂ t A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ ⊥
    → Γ ⊢ ☆³ t₃ ∶ ☆² t₂ ∶ ☆ t ∶ A
★⁴_ {t₃} {t₂} {t} =
    ★ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}


-- --------------------------------------------------------------------------
--
-- Quotation


quo : ∀{B Γ} → Γ ⊢ B → Tm
quo (𝒗[ n ] i)            = 𝑣[ suc n ] ix i
quo (𝝀ⁿ_ {n} 𝒟)           = 𝜆[ suc n ] quo 𝒟
quo (_∙ⁿ_ {n} 𝒟 𝒞)        = quo 𝒟 ∘[ suc n ] quo 𝒞
quo (𝒑ⁿ⟨_,_⟩ {n} 𝒟 𝒞)     = 𝑝[ suc n ]⟨ quo 𝒟 , quo 𝒞 ⟩
quo (𝝅₀ⁿ_ {n} 𝒟)          = 𝜋₀[ suc n ] quo 𝒟
quo (𝝅₁ⁿ_ {n} 𝒟)          = 𝜋₁[ suc n ] quo 𝒟
quo (𝜾₀ⁿ_ {n} 𝒟)          = 𝜄₀[ suc n ] quo 𝒟
quo (𝜾₁ⁿ_ {n} 𝒟)          = 𝜄₁[ suc n ] quo 𝒟
quo (𝒄ⁿ[_▷_∣_] {n} 𝒟 𝒞 ℰ) = 𝑐[ suc n ][ quo 𝒟 ▷ quo 𝒞 ∣ quo ℰ ]
quo (⬆ⁿ_ {n} 𝒟)           = ⇑[ suc n ] quo 𝒟
quo (⬇ⁿ_ {n} 𝒟)           = ⇓[ suc n ] quo 𝒟
quo (★ⁿ_ {n} 𝒟)           = ☆[ suc n ] quo 𝒟


-- --------------------------------------------------------------------------
--
-- Internalisation (theorem 1, p. 29 [1]; lemma 5.4, pp. 9–10 [2])


-- A , A₂ , … , Aₘ ⊢ B ⇒
--   x ∶ A , x₂ ∶ A₂ , … xₘ ∶ Aₘ ⊢ t (x , x₂ , … , xₘ) ∶ B
int⊢ : ∀{B Γ}
    → (𝒟 : Γ ⊢ B)
    → Γ ⊢ quo 𝒟 ∶ B

int⊢ (𝒗[ n ] i)      = 𝒗[ suc n ] i
int⊢ (𝝀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝀ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)

int⊢ (_∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    _∙ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} {𝐬 = quo 𝒞 ∷ 𝐬} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    𝒑ⁿ⟨_,_⟩ {𝐭 = quo 𝒟 ∷ 𝐭} {𝐬 = quo 𝒞 ∷ 𝐬} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝝅₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₀ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝝅₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₁ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝜾₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₀ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (𝜾₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₁ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)

int⊢ (𝒄ⁿ[_▷_∣_] {𝐭 = 𝐭} {𝐬 = 𝐬} {𝐮 = 𝐮} 𝒟 𝒞 ℰ) =
    𝒄ⁿ[_▷_∣_] {𝐭 = quo 𝒟 ∷ 𝐭} {𝐬 = quo 𝒞 ∷ 𝐬}
                              {𝐮 = quo ℰ ∷ 𝐮} (int⊢ 𝒟) (int⊢ 𝒞)
                                                        (int⊢ ℰ)

int⊢ (⬆ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬆ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (⬇ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬇ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)
int⊢ (★ⁿ_ {𝐭 = 𝐭} 𝒟) = ★ⁿ_ {𝐭 = quo 𝒟 ∷ 𝐭} (int⊢ 𝒟)


-- --------------------------------------------------------------------------
--
-- Weakening


wk∈ : ∀{A Δ}
    → (Γ : Cx)    → A ∈ (∅ „ Γ)
    → A ∈ (Δ „ Γ)
wk∈ ∅       ()
wk∈ (Γ , A) 𝐙     = 𝐙
wk∈ (Γ , A) (𝐒 i) = 𝐒 (wk∈ Γ i)


ix-wk∈ : ∀{A : Ty} {Γ : Cx} → ix {!A ∈ Γ!} ≡ ix {!!}
ix-wk∈ = {!!}


wk⊢ : ∀{A Δ}
    → (Γ : Cx)    → ∅ „ Γ ⊢ A
    → Δ „ Γ ⊢ A

-- Goal: Δ „ Γ ⊢ 𝑣ⁿ (replicate (ix i)) ∵ .A
-- Have: Δ „ Γ ⊢ 𝑣ⁿ (replicate (ix (wk∈ Γ i))) ∵ .A

wk⊢ Γ (𝒗[ n ] i)          = {!𝒗[ n ] wk∈ Γ i!} -- 𝒗[ {!n!} ] wk∈ Γ i
wk⊢ Γ (𝝀ⁿ_ {n} {𝐭} {A} 𝒟) = 𝝀ⁿ_ {𝐭 = 𝐭} (wk⊢ (Γ , A) 𝒟)

wk⊢ Γ (_∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    _∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

wk⊢ Γ (𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
    𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

wk⊢ Γ (𝝅₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝝅₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝜾₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (𝜾₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)

wk⊢ Γ (𝒄ⁿ[_▷_∣_] {n} {𝐭} {𝐬} {𝐮} {A} {B} 𝒟 𝒞 ℰ) =
    𝒄ⁿ[_▷_∣_] {𝐭 = 𝐭} {𝐬 = 𝐬}
                      {𝐮 = 𝐮} (wk⊢ Γ 𝒟) (wk⊢ (Γ , A) 𝒞)
                                         (wk⊢ (Γ , B) ℰ)

wk⊢ Γ (⬆ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬆ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (⬇ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬇ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
wk⊢ Γ (★ⁿ_ {𝐭 = 𝐭} 𝒟) = ★ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)


-- --------------------------------------------------------------------------
--
-- Constructive necessitation (corollary 5.5, p. 10 [2])


nec : ∀{A}
    → (𝒟 : ∅ ⊢ A)
    → ⊩ quo 𝒟 ∶ A
nec 𝒟 = wk⊢ ∅ (int⊢ 𝒟)


-- -- --------------------------------------------------------------------------
-- --
-- -- Examples


-- -- Some theorems of propositional logic
-- module PL where
--   I : ∀{A}
--       → ⊩ A ⊃ A
--   I = 𝝀 𝒗 𝟎

--   K : ∀{A B}
--       → ⊩ A ⊃ B ⊃ A
--   K = 𝝀 𝝀 𝒗 𝟏

--   S : ∀{A B C}
--       → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
--   S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

--   X1 : ∀{A B}
--       → ⊩ A ⊃ B ⊃ A ∧ B
--   X1 = 𝝀 𝝀 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩


-- -- Some derived theorems
-- module PLExamples where
--   -- □ (A ⊃ A)
--   I² : ∀{A}
--       → ⊩ 𝜆 𝑣 0 ∶ (A ⊃ A)
--   I² = nec PL.I

--   -- □ □ (A ⊃ A)
--   I³ : ∀{A}
--       → ⊩ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (A ⊃ A)
--   I³ = nec I²

--   -- □ (A ⊃ B ⊃ A)
--   K² : ∀{A B}
--       → ⊩ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
--   K² = nec PL.K

--   -- □ □ (A ⊃ B ⊃ A)
--   K³ : ∀{A B}
--       → ⊩ 𝜆² 𝜆² 𝑣 1 ∶ 𝜆 𝜆 𝑣 1 ∶ (A ⊃ B ⊃ A)
--   K³ = nec K²

--   -- □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
--   S² : ∀{A B C}
--       → ⊩ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
--           ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
--   S² = nec PL.S

--   -- □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
--   S³ : ∀{A B C}
--       → ⊩ 𝜆² 𝜆² 𝜆² (𝑣 2 ∘² 𝑣 0) ∘² (𝑣 1 ∘² 𝑣 0)
--           ∶ 𝜆 𝜆 𝜆 (𝑣 2 ∘ 𝑣 0) ∘ (𝑣 1 ∘ 𝑣 0)
--               ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
--   S³ = nec S²


-- -- Some theorems of modal logic S4
-- module S4 where
--   -- □ (A ⊃ B) ⊃ □ A ⊃ □ B
--   K : ∀{f x A B}
--       → ⊩ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
--   K = 𝝀 𝝀 (𝒗 𝟏 ∙² 𝒗 𝟎)

--   -- □ A ⊃ A
--   T : ∀{x A}
--       → ⊩ x ∶ A ⊃ A
--   T = 𝝀 ⬇ 𝒗 𝟎

--   -- □ A ⊃ □ □ A
--   #4 : ∀{x A}
--       → ⊩ x ∶ A ⊃ ! x ∶ x ∶ A
--   #4 = 𝝀 ⬆ 𝒗 𝟎

--   -- □ A ⊃ □ B ⊃ □ □ (A ∧ B)
--   X1 : ∀{x y A B}
--       → ⊩ x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
--   X1 = 𝝀 𝝀 ⬆ 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

--   -- □ A ⊃ □ B ⊃ □ (A ∧ B)
--   X2 : ∀{x y A B}
--       → ⊩ x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
--   X2 = 𝝀 𝝀 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

--   -- □ A ∧ □ B ⊃ □ □ (A ∧ B)
--   X3 : ∀{x y A B}
--       → ⊩ x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
--   X3 = 𝝀 ⬆ 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩

--   -- □ A ∧ □ B ⊃ □ (A ∧ B)
--   X4 : ∀{x y A B}
--       → ⊩ x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
--   X4 = 𝝀 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩


-- -- Some more derived theorems
-- module S4Examples where
--   -- □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
--   K² : ∀{f x A B}
--       → ⊩ 𝜆 𝜆 𝑣 1 ∘² 𝑣 0 ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B)
--   K² = nec S4.K


-- -- --------------------------------------------------------------------------
-- --
-- -- Original examples


-- -- Example 1 (p. 28 [1])
-- module Example1 where
--   -- □ (□ A ⊃ A)
--   E11 : ∀{x A}
--       → ⊩ 𝜆 ⇓ 𝑣 0 ∶ (x ∶ A ⊃ A)
--   E11 = nec S4.T

--   -- □ (□ A ⊃ □ □ A)
--   E12 : ∀{x A}
--       → ⊩ 𝜆 ⇑ 𝑣 0 ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
--   E12 = nec S4.#4

--   -- □ □ (A ⊃ B ⊃ A ∧ B)
--   E13 : ∀{A B}
--       → ⊩ 𝜆² 𝜆² 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ 𝜆 𝜆 𝑝⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
--   E13 = nec (nec PL.X1)

--   -- □ (□ A ⊃ □ B ⊃ □ □ (A ∧ B))
--   E14 : ∀{x y A B}
--       → ⊩ 𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩
--           ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
--   E14 = nec S4.X1


-- -- Some more variants of example 1
-- module Example1a where
--   -- □ (□ A ⊃ □ B ⊃ □ (A ∧ B))
--   E14a : ∀{x y A B}
--       → ⊩ 𝜆 𝜆 𝑝²⟨ 𝑣 1 , 𝑣 0 ⟩ ∶ (x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
--   E14a = nec S4.X2

--   -- □ (□ A ∧ □ B ⊃ □ □ (A ∧ B))
--   E14c : ∀{x y A B}
--       → ⊩ 𝜆 ⇑ 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩
--           ∶ (x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
--   E14c = nec S4.X3

--   -- □ (□ A ∧ □ B ⊃ □ (A ∧ B))
--   E14b : ∀{x y A B}
--       → ⊩ 𝜆 𝑝²⟨ 𝜋₀ 𝑣 0 , 𝜋₁ 𝑣 0 ⟩ ∶ (x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
--   E14b = nec S4.X4


-- -- Example 2 (pp. 31–32 [1])
-- module Example2 where
--   E2 : ∀{x A}
--       → ⊩ 𝜆² ⇓² ⇑² 𝑣² 0 ∶ 𝜆 ⇓ ⇑ 𝑣 0 ∶ (x ∶ A ⊃ x ∶ A)
--   E2 = 𝝀³ ⬇³ ⬆³ 𝒗³ 𝟎

--   E2a : ∀{x A}
--       → ⊩ 𝜆² 𝑣² 0 ∶ 𝜆 𝑣 0 ∶ (x ∶ A ⊃ x ∶ A)
--   E2a = 𝝀³ 𝒗³ 𝟎


-- -- -- --------------------------------------------------------------------------
-- -- --
-- -- -- Additional examples


-- -- -- De Morgan’s laws
-- -- module DeMorgan where
-- --   -- (A ⊃ ⊥) ∧ (B ⊃ ⊥) ⫗ (A ∨ B) ⊃ ⊥
-- --   L1 : ∀{A B}
-- --       → ⊩ ¬ A ∧ ¬ B ⫗ ¬ (A ∨ B)
-- --   L1 = 𝒑⟨ 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ]
-- --         , 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩ ⟩

-- --   -- (A ⊃ ⊥) ∨ (B ⊃ ⊥) ⊃ (A ⊃ ⊥) ∧ B
-- --   L2 : ∀{A B}
-- --       → ⊩ ¬ A ∨ ¬ B ⊃ ¬ (A ∧ B)
-- --   L2 = 𝝀 𝝀 𝒄[ 𝒗 𝟏 ▷ 𝒗 𝟎 ∙ 𝝅₀ 𝒗 𝟏 ∣ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟏 ]


-- -- -- Explosions and contradictions
-- -- module ExploCon where
-- --   X1 : ∀{A}
-- --       → ⊩ ⊥ ⊃ A
-- --   X1 = 𝝀 ★ 𝒗 𝟎

-- --   -- □ (⊥ ⊃ A)
-- --   X1² : ∀{A}
-- --       → ⊩ 𝜆 ☆ 𝑣 0 ∶ (⊥ ⊃ A)
-- --   X1² = nec X1

-- --   -- □ ⊥ ⊃ □ A
-- --   X2 : ∀{x A}
-- --       → ⊩ x ∶ ⊥ ⊃ ☆ x ∶ A
-- --   X2 = 𝝀 ★² 𝒗 𝟎

-- --   X3 : ∀{A}
-- --       → ⊩ ¬ A ⊃ A ⊃ ⊥
-- --   X3 = 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟎

-- --   -- □ (¬ A) ⊃ □ A ⊃ □ ⊥
-- --   X4 : ∀{x y A}
-- --       → ⊩ x ∶ (¬ A) ⊃ y ∶ A ⊃ x ∘ y ∶ ⊥
-- --   X4 = 𝝀 𝝀 𝒗 𝟏 ∙² 𝒗 𝟎

-- --   -- □ (¬ A) ⊃ □ A ⊃ □ □ ⊥
-- --   X5 : ∀{x y A}
-- --       → ⊩ x ∶ (¬ A) ⊃ y ∶ A ⊃ ! (x ∘ y) ∶ x ∘ y ∶ ⊥
-- --   X5 = 𝝀 𝝀 ⬆ 𝒗 𝟏 ∙² 𝒗 𝟎


-- -- -- --------------------------------------------------------------------------
-- -- --
-- -- -- Further examples


-- -- module Idempotence where
-- --   ⊃-idem : ∀{A}
-- --       → ⊩ A ⊃ A ⫗ ⊤
-- --   ⊃-idem = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
-- --             , 𝝀 𝝀 𝒗 𝟎 ⟩

-- --   ∧-idem : ∀{A}
-- --       → ⊩ A ∧ A ⫗ A
-- --   ∧-idem = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
-- --             , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝒗 𝟎 ⟩ ⟩

-- --   ∨-idem : ∀{A}
-- --       → ⊩ A ∨ A ⫗ A
-- --   ∨-idem = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ 𝒗 𝟎 ]
-- --             , 𝝀 𝜾₀ 𝒗 𝟎 ⟩


-- -- module Commutativity where
-- --   ∧-comm : ∀{A B}
-- --       → ⊩ A ∧ B ⫗ B ∧ A
-- --   ∧-comm = 𝒑⟨ 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩
-- --             , 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩ ⟩

-- --   ∨-comm : ∀{A B}
-- --       → ⊩ A ∨ B ⫗ B ∨ A
-- --   ∨-comm = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ]
-- --             , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ] ⟩


-- -- module Associativity where
-- --   ∧-assoc : ∀{A B C}
-- --       → ⊩ A ∧ (B ∧ C) ⫗ (A ∧ B) ∧ C
-- --   ∧-assoc = 𝒑⟨ 𝝀 𝒑⟨ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₀ 𝝅₁ 𝒗 𝟎 ⟩ , 𝝅₁ 𝝅₁ 𝒗 𝟎 ⟩
-- --              , 𝝀 𝒑⟨ 𝝅₀ 𝝅₀ 𝒗 𝟎 , 𝒑⟨ 𝝅₁ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩ ⟩ ⟩

-- --   ∨-assoc : ∀{A B C}
-- --       → ⊩ A ∨ (B ∨ C) ⫗ (A ∨ B) ∨ C
-- --   ∨-assoc = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₁ 𝒗 𝟎 ] ]
-- --              , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝜾₀ 𝒗 𝟎 ] ∣ 𝜾₁ 𝜾₁ 𝒗 𝟎 ] ⟩


-- -- module Distributivity where
-- --   ⊃-dist-∧ : ∀{A B C}
-- --       → ⊩ A ⊃ (B ∧ C) ⫗ (A ⊃ B) ∧ (A ⊃ C)
-- --   ⊃-dist-∧ = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝝅₀ (𝒗 𝟏 ∙ 𝒗 𝟎) , 𝝀 𝝅₁ (𝒗 𝟏 ∙ 𝒗 𝟎) ⟩
-- --               , 𝝀 𝝀 𝒑⟨ 𝝅₀ 𝒗 𝟏 ∙ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟏 ∙ 𝒗 𝟎 ⟩ ⟩

-- --   ∧-dist-∨ : ∀{A B C}
-- --       → ⊩ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
-- --   ∧-dist-∨ = 𝒑⟨ 𝝀 𝒄[ 𝝅₁ 𝒗 𝟎 ▷ 𝜾₀ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ∣ 𝜾₁ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ]
-- --               , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₀ 𝝅₁ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ] ⟩

-- --   ∨-dist-∧ : ∀{A B C}
-- --       → ⊩ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
-- --   ∨-dist-∧ = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝜾₀ 𝒗 𝟎 , 𝜾₀ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝜾₁ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ]
-- --               , 𝝀 𝒄[ 𝝅₀ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝝅₁ 𝒗 𝟏 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ] ] ⟩


-- -- module Untitled where
-- --   ⊃-law : ∀{A B C}
-- --       → ⊩ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
-- --   ⊃-law = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟎)

-- --   ⊃-∧-law : ∀{A B C}
-- --       → ⊩ A ⊃ B ⊃ C ⫗ (A ∧ B) ⊃ C
-- --   ⊃-∧-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟏 ∙ 𝝅₀ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟎
-- --              , 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ⟩

-- --   ∨-⊃-∧-law : ∀{A B C}
-- --       → ⊩ (A ∨ B) ⊃ C ⫗ (A ⊃ C) ∧ (B ⊃ C)
-- --   ∨-⊃-∧-law = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩
-- --                , 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ] ⟩


-- -- module Trivial where
-- --   ⊃-⊤-law : ∀{A}
-- --       → ⊩ A ⊃ ⊤ ⫗ ⊤
-- --   ⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
-- --               , 𝝀 𝝀 𝒗 𝟏 ⟩

-- --   ⊤-⊃-law : ∀{A}
-- --       → ⊩ ⊤ ⊃ A ⫗ A
-- --   ⊤-⊃-law = 𝒑⟨ 𝝀 𝒗 𝟎 ∙ (𝝀 𝒗 𝟎)
-- --               , 𝝀 𝝀 𝒗 𝟏 ⟩

-- --   ⊥-⊃-⊤-law : ∀{A}
-- --       → ⊩ ⊥ ⊃ A ⫗ ⊤
-- --   ⊥-⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
-- --                  , 𝝀 𝝀 ★ 𝒗 𝟎 ⟩

-- --   ∧-⊥-law : ∀{A}
-- --       → ⊩ A ∧ ⊥ ⫗ ⊥
-- --   ∧-⊥-law = 𝒑⟨ 𝝀 𝝅₁ 𝒗 𝟎
-- --                 , 𝝀 ★ 𝒗 𝟎 ⟩

-- --   ∨-⊥-law : ∀{A}
-- --       → ⊩ A ∨ ⊥ ⫗ A
-- --   ∨-⊥-law = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ ★ 𝒗 𝟎 ]
-- --                 , 𝝀 𝜾₀ 𝒗 𝟎 ⟩

-- --   ∧-⊤-law : ∀{A}
-- --       → ⊩ A ∧ ⊤ ⫗ A
-- --   ∧-⊤-law = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
-- --                 , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝝀 𝒗 𝟎 ⟩ ⟩

-- --   ∨-⊤-law : ∀{A}
-- --       → ⊩ A ∨ ⊤ ⫗ ⊤
-- --   ∨-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
-- --                 , 𝝀 𝜾₁ 𝒗 𝟎 ⟩
