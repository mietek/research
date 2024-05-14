{-

An extension of reflective λ-calculus
=====================================

Miëtek Bak  <mietek@bak.io>


A work-in-progress implementation of the Alt-Artëmov system λ∞,
extended with disjunction and falsehood.

See a summary of the basic and extended system:
https://www.dropbox.com/s/wz9ktvsauhkywxc/2016-03-28-extension.pdf

Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") (":." "∵")
     ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("v4" "𝑣⁴") ("vn" "𝑣ⁿ")
     ("fv" "𝑓𝑣") ("fv2" "𝑓𝑣²") ("fv3" "𝑓𝑣³") ("fv4" "𝑓𝑣⁴") ("fvn" "𝑓𝑣ⁿ")
     ("bv" "𝑏𝑣") ("bv2" "𝑏𝑣²") ("bv3" "𝑏𝑣³") ("bv4" "𝑏𝑣⁴") ("bvn" "𝑏𝑣ⁿ")
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
     ("t" "𝑡") ("t2" "𝑡²") ("t3" "𝑡³") ("t4" "𝑡⁴") ("tn" "𝑡ⁿ")
     ("x" "☆") ("x2" "☆²") ("x3" "☆³") ("x4" "☆⁴") ("xn" "☆ⁿ")
     ("b" "□")
     ("S" "𝕊") ("Z" "ℤ")
     ("0" "𝟘") ("1" "𝟙") ("2" "𝟚") ("3" "𝟛") ("4" "𝟜")
     ("mv" "𝒗") ("mv2" "𝒗²") ("mv3" "𝒗³") ("mv4" "𝒗⁴") ("mvn" "𝒗ⁿ")
     ("mfv" "𝒇𝒗") ("mfv2" "𝒇𝒗²") ("mfv3" "𝒇𝒗³") ("mfv4" "𝒇𝒗⁴") ("mfvn" "𝒇𝒗ⁿ")
     ("mbv" "𝒃𝒗") ("mbv2" "𝒃𝒗²") ("mbv3" "𝒃𝒗³") ("mbv4" "𝒃𝒗⁴") ("mbvn" "𝒃𝒗ⁿ")
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
     ("mt" "𝒕") ("mt2" "𝒕²") ("mt3" "𝒕³") ("mt4" "𝒕⁴") ("mtn" "𝒕ⁿ")
     ("mx" "★") ("mx2" "★²") ("mx3" "★³") ("mx4" "★⁴") ("mxn" "★ⁿ")
     ("mb" "■")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("ss" "𝐬") ("ts" "𝐭") ("us" "𝐮") ("xs" "𝐱") ("ys" "𝐲") ("zs" "𝐳")
     ("C" "𝒞") ("D" "𝒟") ("E" "ℰ")
     ("N" "ℕ"))))


[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus.
     Proceedings of the 2001 International Seminar on Proof Theory in
     Computer Science (PTCS’01), Lecture Notes in Computer Science,
     vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

[2]: Artëmov, S. (2001) Explicit provability and constructive semantics.
     Bulletin of Symbolic Logic, vol. 7, no. 1, pp. 1–36.
     http://dx.doi.org/10.2307/2687821

-}


module AltArtemov-WIP3 where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; subst)

infixl 9 !_ 𝑣_ 𝒗_
infixl 9 ☆_ ☆²_ -- ☆³_ ☆⁴_ ☆ⁿ_
infixl 9 ★_ ★²_ -- ★³_ ★⁴_ ★ⁿ_
infixl 8 𝜋₀_ 𝜋₀²_ -- 𝜋₀³_ 𝜋₀⁴_ 𝜋₀ⁿ_
infixl 8 𝝅₀_ 𝝅₀²_ -- 𝝅₀³_ 𝝅₀⁴_ 𝝅₀ⁿ_
infixl 8 𝜋₁_ 𝜋₁²_ -- 𝜋₁³_ 𝜋₁⁴_ 𝜋₁ⁿ_
infixl 8 𝝅₁_ 𝝅₁²_ -- 𝝅₁³_ 𝝅₁⁴_ 𝝅₁ⁿ_
infixl 8 𝜄₀_ 𝜄₀²_ -- 𝜄₀³_ 𝜄₀⁴_ 𝜄₀ⁿ_
infixl 8 𝜾₀_ 𝜾₀²_ -- 𝜾₀³_ 𝜾₀⁴_ 𝜾₀ⁿ_
infixl 8 𝜄₁_ 𝜄₁²_ -- 𝜄₁³_ 𝜄₁⁴_ 𝜄₁ⁿ_
infixl 7 𝜾₁_ 𝜾₁²_ -- 𝜾₁³_ 𝜾₁⁴_ 𝜾₁ⁿ_
infixl 7 _∘_ _∘²_ -- _∘³_ _∘⁴_ _∘ⁿ_
infixl 7 _∙_ _∙²_ -- _∙³_ _∙⁴_ _∙ⁿ_
infixr 6 ⇑_ ⇑²_ -- ⇑³_ ⇑⁴_ ⇑ⁿ_
infixr 6 ⬆_ ⬆²_ -- ⬆³_ ⬆⁴_ ⬆ⁿ_
infixr 6 ⇓_ ⇓²_ -- ⇓³_ ⇓⁴_ ⇓ⁿ_
infixr 6 ⬇_ ⬇²_ -- ⬇³_ ⬇⁴_ ⬇ⁿ_
infixr 5 𝜆_ 𝜆²_ -- 𝜆³_ 𝜆⁴_ 𝜆ⁿ_
infixr 5 𝝀_ 𝝀²_ -- 𝝀³_ 𝝀⁴_ 𝝀ⁿ_
infixr 5 _∶_ -- _∵_
infixr 4 ¬_
infixl 4 _∧_
infixl 3 _∨_ _,_ _„_
infixr 2 _⊃_
infixr 1 _⫗_
infixr 0 _⊢_∶ⁿ_ _⊢_ _⊢_∵_ -- ⊩_


-- --------------------------------------------------------------------------
--
-- Well-scoped syntax


-- Untyped terms
data Tm (m : ℕ) : Set where
  -- Variable reference
  𝑣_ : Fin m → Tm m

  -- Abstraction (⊃I) at level n
  𝜆[_]_ : ℕ → Tm (suc m) → Tm m

  -- Application (⊃E) at level n
  _∘[_]_ : Tm m → ℕ → Tm m → Tm m

  -- Pair (∧I) at level n
  𝑝[_]⟨_,_⟩ : ℕ → Tm m → Tm m → Tm m

  -- 0th projection (∧E₀) at level n
  𝜋₀[_]_ : ℕ → Tm m → Tm m

  -- 1st projection (∧E₁) at level n
  𝜋₁[_]_ : ℕ → Tm m → Tm m

  -- 0th injection (∨I₀) at level n
  𝜄₀[_]_ : ℕ → Tm m → Tm m

  -- 1st injection (∨I₁) at level n
  𝜄₁[_]_ : ℕ → Tm m → Tm m

  -- Case split (∨E) at level n
  𝑐[_][_▷_∣_] : ℕ → Tm m → Tm (suc m) → Tm (suc m) → Tm m

  -- Artëmov’s “proof checker”
  !_ : Tm m → Tm m

  -- Reification at level n
  ⇑[_]_ : ℕ → Tm m → Tm m

  -- Reflection at level n
  ⇓[_]_ : ℕ → Tm m → Tm m

  -- Explosion (⊥E) at level n
  ☆[_]_ : ℕ → Tm m → Tm m


-- Types
data Ty : Set where
  -- Implication
  _⊃_ : Ty → Ty → Ty

  -- Conjunction
  _∧_ : Ty → Ty → Ty

  -- Disjunction
  _∨_ : Ty → Ty → Ty

  -- Explicit provability
  _∶_ : Tm 0 → Ty → Ty

  -- Falsehood
  ⊥ : Ty


-- --------------------------------------------------------------------------
--
-- Example types


-- Truth
⊤ : Ty
⊤ = ⊥ ⊃ ⊥

-- Negation
¬_ : Ty → Ty
¬ A = A ⊃ ⊥

-- Equivalence
_⫗_ : Ty → Ty → Ty
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)


-- --------------------------------------------------------------------------
--
-- Notation for untyped terms at level 1


𝜆_ : ∀{m} → Tm (suc m) → Tm m
𝜆 t = 𝜆[ 1 ] t

_∘_ : ∀{m} → Tm m → Tm m → Tm m
t ∘ s = t ∘[ 1 ] s

𝑝⟨_,_⟩ : ∀{m} → Tm m → Tm m → Tm m
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝜋₀_ : ∀{m} → Tm m → Tm m
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₁_ : ∀{m} → Tm m → Tm m
𝜋₁ t = 𝜋₁[ 1 ] t

𝜄₀_ : ∀{m} → Tm m → Tm m
𝜄₀ t = 𝜄₀[ 1 ] t

𝜄₁_ : ∀{m} → Tm m → Tm m
𝜄₁ t = 𝜄₁[ 1 ] t

𝑐[_▷_∣_] : ∀{m} → Tm m → Tm (suc m) → Tm (suc m) → Tm m
𝑐[ t ▷ s ∣ r ] = 𝑐[ 1 ][ t ▷ s ∣ r ]

⇑_ : ∀{m} → Tm m → Tm m
⇑ t = ⇑[ 1 ] t

⇓_ : ∀{m} → Tm m → Tm m
⇓ t = ⇓[ 1 ] t

☆_ : ∀{m} → Tm m → Tm m
☆ t = ☆[ 1 ] t


-- --------------------------------------------------------------------------
--
-- Notation for untyped terms at level 2


𝜆²_ : ∀{m} → Tm (suc m) → Tm m
𝜆² t₂ = 𝜆[ 2 ] t₂

_∘²_ : ∀{m} → Tm m → Tm m → Tm m
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝²⟨_,_⟩ : ∀{m} → Tm m → Tm m → Tm m
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀²_ : ∀{m} → Tm m → Tm m
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁²_ : ∀{m} → Tm m → Tm m
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

𝜄₀²_ : ∀{m} → Tm m → Tm m
𝜄₀² t₂ = 𝜄₀[ 2 ] t₂

𝜄₁²_ : ∀{m} → Tm m → Tm m
𝜄₁² t₂ = 𝜄₁[ 2 ] t₂

𝑐²[_▷_∣_] : ∀{m} → Tm m → Tm (suc m) → Tm (suc m) → Tm m
𝑐²[ t₂ ▷ s₂ ∣ r₂ ] = 𝑐[ 2 ][ t₂ ▷ s₂ ∣ r₂ ]

⇑²_ : ∀{m} → Tm m → Tm m
⇑² t₂ = ⇑[ 2 ] t₂

⇓²_ : ∀{m} → Tm m → Tm m
⇓² t₂ = ⇓[ 2 ] t₂

☆²_ : ∀{m} → Tm m → Tm m
☆² t = ☆[ 2 ] t


-- --------------------------------------------------------------------------
--
-- Notation for untyped terms at level 3

{-
𝜆³_ : Tm → Tm
𝜆³ t₃ = 𝜆[ 3 ] t₃

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
-- Notation for untyped terms at level 4


𝜆⁴_ : Tm → Tm
𝜆⁴ t₄ = 𝜆[ 4 ] t₄

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
-}

-- --------------------------------------------------------------------------
--
-- Vector notation (p. 27 [1])


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
Tms : ℕ → ℕ → Set
Tms m = Vec (Tm m)


-- 𝑣 x ∶ 𝑣 x ∶ … ∶ 𝑣 x
𝑣[_]_ : ∀{m} → (n : ℕ) → Fin m → Tms m n
𝑣[ zero ]  i = []
𝑣[ suc n ] i = 𝑣 i ∷ 𝑣[ n ] i

-- 𝜆ⁿ tₙ ∶ 𝜆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜆 t
𝜆ⁿ_ : ∀{m n} → Tms (suc m) n → Tms m n
𝜆ⁿ_ = map# 𝜆[_]_

-- tₙ ∘ⁿ sₙ ∶ tₙ₋₁ ∘ⁿ⁻¹ ∶ sₙ₋₁ ∶ … ∶ t ∘ s
_∘ⁿ_ : ∀{m n} → Tms m n → Tms m n → Tms m n
_∘ⁿ_ = map2# (λ n t s → t ∘[ n ] s)

-- 𝑝ⁿ⟨ tₙ , sₙ ⟩ ∶ 𝑝ⁿ⁻¹⟨ tₙ₋₁ , sₙ₋₁ ⟩ ∶ … ∶ p⟨ t , s ⟩
𝑝ⁿ⟨_,_⟩ : ∀{m n} → Tms m n → Tms m n → Tms m n
𝑝ⁿ⟨_,_⟩ = map2# 𝑝[_]⟨_,_⟩

-- 𝜋₀ⁿ tₙ ∶ 𝜋₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₀ t
𝜋₀ⁿ_ : ∀{m n} → Tms m n → Tms m n
𝜋₀ⁿ_ = map# 𝜋₀[_]_

-- 𝜋₁ⁿ tₙ ∶ 𝜋₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜋₁ t
𝜋₁ⁿ_ : ∀{m n} → Tms m n → Tms m n
𝜋₁ⁿ_ = map# 𝜋₁[_]_

-- 𝜄₀ⁿ tₙ ∶ 𝜄₀ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₀ t
𝜄₀ⁿ_ : ∀{m n} → Tms m n → Tms m n
𝜄₀ⁿ_ = map# 𝜄₀[_]_

-- 𝜄₁ⁿ tₙ ∶ 𝜄₁ⁿ⁻¹ tₙ₋₁ ∶ … ∶ 𝜄₁ t
𝜄₁ⁿ_ : ∀{m n} → Tms m n → Tms m n
𝜄₁ⁿ_ = map# 𝜄₁[_]_

-- 𝑐ⁿ[ tₙ ▷ sₙ ∣ rₙ ] ∶ 𝑐ⁿ⁻¹[ tₙ₋₁ ▷ sₙ₋₁ ∣ rₙ₋₁ ] ∶ … ∶ 𝑐[ t ▷ s ∣ r ]
𝑐ⁿ[_▷_∣_] : ∀{m n} → Tms m n → Tms (suc m) n → Tms (suc m) n → Tms m n
𝑐ⁿ[_▷_∣_] = map3# 𝑐[_][_▷_∣_]

-- ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇑ⁿ_ : ∀{m n} → Tms m n → Tms m n
⇑ⁿ_ = map# ⇑[_]_

-- ⇓ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t
⇓ⁿ_ : ∀{m n} → Tms m n → Tms m n
⇓ⁿ_ = map# ⇓[_]_

-- ☆ⁿ tₙ ∶ ☆ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ☆ t
☆ⁿ_ : ∀{m n} → Tms m n → Tms m n
☆ⁿ_ = map# ☆[_]_


-- --------------------------------------------------------------------------
--
-- Well-typed syntax


-- Hypotheses
Hyp : Set
Hyp = ℕ × Ty


-- Contexts
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Hyp → Cx


nat : Cx → ℕ
nat ∅       = zero
nat (Γ , x) = suc (nat Γ)


_„_ : Cx → Cx → Cx
Γ „ ∅       = Γ
Γ „ (Δ , A) = (Γ „ Δ) , A


-- Context membership
data _∈_ : Hyp → Cx → Set where
  𝐙 : ∀{A Γ}
      → A ∈ (Γ , A)

  𝐒_ : ∀{A B Γ}
      → A ∈ Γ
      → A ∈ (Γ , B)


fin : ∀ {Γ A} → A ∈ Γ → Fin (nat Γ)
fin 𝐙     = zero
fin (𝐒 i) = suc (fin i)


lift : ∀{m} → Tm 0 → Tm m
lift t = {!!}


-- Typed terms
data _⊢_∶ⁿ_ (Γ : Cx) {n : ℕ} : Tms (nat Γ) n → Ty → Set where
  -- Variable reference
  𝒗_ : ∀{A}
      → (i : ⟨ n , A ⟩ ∈ Γ)
      → Γ ⊢ 𝑣[ n ] (fin i) ∶ⁿ A

  -- Abstraction (⊃I) at level n
  𝝀ⁿ_ : ∀{𝐭 : Tms (suc (nat Γ)) n} {A B}
      → Γ , ⟨ n , A ⟩ ⊢ 𝐭 ∶ⁿ B
      → Γ ⊢ 𝜆ⁿ 𝐭 ∶ⁿ A ⊃ B

  -- Application (⊃E) at level n
  _∙ⁿ_ : ∀{𝐭 𝐬 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ A ⊃ B    → Γ ⊢ 𝐬 ∶ⁿ A
      → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∶ⁿ B

  -- Pair (∧I) at level n
  𝒑ⁿ⟨_,_⟩ : ∀{𝐭 𝐬 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ A          → Γ ⊢ 𝐬 ∶ⁿ B
      → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩ ∶ⁿ A ∧ B

  -- 0th projection (∧E₀) at level n
  𝝅₀ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ A ∧ B
      → Γ ⊢ 𝜋₀ⁿ 𝐭 ∶ⁿ A

  -- 1st projection (∧E₁) at level n
  𝝅₁ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ A ∧ B
      → Γ ⊢ 𝜋₁ⁿ 𝐭 ∶ⁿ B

  -- 0th injection (∨I₀) at level n
  𝜾₀ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ A
      → Γ ⊢ 𝜄₀ⁿ 𝐭 ∶ⁿ A ∨ B

  -- 1st injection (∨I₁) at level n
  𝜾₁ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {A B}
      → Γ ⊢ 𝐭 ∶ⁿ B
      → Γ ⊢ 𝜄₁ⁿ 𝐭 ∶ⁿ A ∨ B

  -- Case split (∨E) at level n
  𝒄ⁿ[_▷_∣_] : ∀{𝐭 : Tms (nat Γ) n} {𝐬 𝐮 : Tms (suc (nat Γ)) n} {A B C}
      → Γ ⊢ 𝐭 ∶ⁿ A ∨ B    → Γ , ⟨ n , A ⟩ ⊢ 𝐬 ∶ⁿ C
                           → Γ , ⟨ n , B ⟩ ⊢ 𝐮 ∶ⁿ C
      → Γ ⊢ 𝑐ⁿ[ 𝐭 ▷ 𝐬 ∣ 𝐮 ] ∶ⁿ C

  -- Reification at level n
  ⬆ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {u A}
      → Γ ⊢ 𝐭 ∶ⁿ u ∶ A
      → Γ ⊢ ⇑ⁿ 𝐭 ∶ⁿ ! u ∶ u ∶ A

  -- Reflection at level n
  ⬇ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {u A}
      → Γ ⊢ 𝐭 ∶ⁿ u ∶ A
      → Γ ⊢ ⇓ⁿ 𝐭 ∶ⁿ A

  -- Explosion (⊥E)
  ★ⁿ_ : ∀{𝐭 : Tms (nat Γ) n} {A}
      → Γ ⊢ 𝐭 ∶ⁿ ⊥
      → Γ ⊢ ☆ⁿ 𝐭 ∶ⁿ A


-- Closed terms
⊩_∶ⁿ_  : ∀{n} → Tms 0 n → Ty → Set
⊩ 𝐭 ∶ⁿ A = ∅ ⊢ 𝐭 ∶ⁿ A


-- --------------------------------------------------------------------------
--
-- Notation for context membership


𝟎 : ∀{A Γ}
    → A ∈ (Γ , A)
𝟎 = 𝐙

𝟏 : ∀{A B Γ}
    → A ∈ ((Γ , A) , B)
𝟏 = 𝐒 𝟎

𝟐 : ∀{A B C Γ}
    → A ∈ (((Γ , A) , B) , C)
𝟐 = 𝐒 𝟏

𝟑 : ∀{A B C D Γ}
    → A ∈ ((((Γ , A) , B) , C) , D)
𝟑 = 𝐒 𝟐

𝟒 : ∀{A B C D E Γ}
    → A ∈ (((((Γ , A) , B) , C) , D) , E)
𝟒 = 𝐒 𝟑


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 1


_⊢_ : Cx → Ty → Set
Γ ⊢ A = Γ ⊢ [] ∶ⁿ A


𝝀_ : ∀{Γ A B}
    → Γ , ⟨ 0 , A ⟩ ⊢ B
    → Γ ⊢ A ⊃ B
𝝀_ = 𝝀ⁿ_

_∙_ : ∀{Γ A B}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
_∙_ = _∙ⁿ_

𝒑⟨_,_⟩ : ∀{Γ A B}
    → Γ ⊢ A        → Γ ⊢ B
    → Γ ⊢ A ∧ B
𝒑⟨_,_⟩ = 𝒑ⁿ⟨_,_⟩

𝝅₀_ : ∀{Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
𝝅₀_ = 𝝅₀ⁿ_

𝝅₁_ : ∀{Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
𝝅₁_ = 𝝅₁ⁿ_

𝜾₀_ : ∀{Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A ∨ B
𝜾₀_ = 𝜾₀ⁿ_

𝜾₁_ : ∀{Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A ∨ B
𝜾₁_ = 𝜾₁ⁿ_

𝒄[_▷_∣_] : ∀{Γ A B C}
    → Γ ⊢ A ∨ B    → Γ , ⟨ 0 , A ⟩ ⊢ C
                     → Γ , ⟨ 0 , B ⟩ ⊢ C
    → Γ ⊢ C
𝒄[_▷_∣_] = 𝒄ⁿ[_▷_∣_]

⬆_ : ∀{Γ u A}
    → Γ ⊢ u ∶ A
    → Γ ⊢ ! u ∶ u ∶ A
⬆_ = ⬆ⁿ_

⬇_ : ∀{Γ u A}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
⬇_ = ⬇ⁿ_

★_ : ∀{Γ A}
    → Γ ⊢ ⊥
    → Γ ⊢ A
★_ = ★ⁿ_


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 2


_⊢_∵_ : (Γ : Cx) → Tm (nat Γ) → Ty → Set
Γ ⊢ t ∵ A = Γ ⊢ t ∷ [] ∶ⁿ A


𝝀²_ : ∀{Γ t A B}
    → Γ , ⟨ 1 , A ⟩ ⊢ t ∵ B
    → Γ ⊢ 𝜆 t ∵ A ⊃ B
𝝀²_ = 𝝀ⁿ_

_∙²_ : ∀{Γ t s A B}
    → Γ ⊢ t ∵ A ⊃ B    → Γ ⊢ s ∵ A
    → Γ ⊢ t ∘ s ∵ B
_∙²_ = _∙ⁿ_

𝒑²⟨_,_⟩ : ∀{Γ t s A B}
    → Γ ⊢ t ∵ A          → Γ ⊢ s ∵ B
    → Γ ⊢ 𝑝⟨ t , s ⟩ ∵ A ∧ B
𝒑²⟨_,_⟩ = 𝒑ⁿ⟨_,_⟩

𝝅₀²_ : ∀{Γ t A B}
    → Γ ⊢ t ∵ A ∧ B
    → Γ ⊢ 𝜋₀ t ∵ A
𝝅₀²_ = 𝝅₀ⁿ_

𝝅₁²_ : ∀{Γ t A B}
    → Γ ⊢ t ∵ A ∧ B
    → Γ ⊢ 𝜋₁ t ∵ B
𝝅₁²_ = 𝝅₁ⁿ_

𝜾₀²_ : ∀{Γ t A B}
    → Γ ⊢ t ∵ A
    → Γ ⊢ 𝜄₀ t ∵ A ∨ B
𝜾₀²_ = 𝜾₀ⁿ_

𝜾₁²_ : ∀{Γ t A B}
    → Γ ⊢ t ∵ B
    → Γ ⊢ 𝜄₁ t ∵ A ∨ B
𝜾₁²_ = 𝜾₁ⁿ_

𝒄²[_▷_∣_] : ∀{Γ t s u A B C}
    → Γ ⊢ t ∵ A ∨ B    → Γ , ⟨ 1 , A ⟩ ⊢ s ∵ C
                         → Γ , ⟨ 1 , B ⟩ ⊢ u ∵ C
    → Γ ⊢ 𝑐[ t ▷ s ∣ u ] ∵ C
𝒄²[_▷_∣_] = 𝒄ⁿ[_▷_∣_]

⬆²_ : ∀{Γ t u A}
    → Γ ⊢ t ∵ u ∶ A
    → Γ ⊢ ⇑ t ∵ ! u ∶ u ∶ A
⬆²_ = ⬆ⁿ_

⬇²_ : ∀{Γ t u A}
    → Γ ⊢ t ∵ u ∶ A
    → Γ ⊢ ⇓ t ∵ A
⬇²_ = ⬇ⁿ_

★²_ : ∀{Γ t A}
    → Γ ⊢ t ∵ ⊥
    → Γ ⊢ ☆ t ∵ A
★²_ = ★ⁿ_


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 3


{-𝝀³_ : ∀{t₂ t A B Γ}
    → Γ , ⟨ 2 , A ⟩ ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ 𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)
𝝀³_ {t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₂ ∷ t ∷ []}

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
    → Γ ⊢ t₂ ∶ t ∶ (A ∨ B)    → Γ , ⟨ 2 , A ⟩ ⊢ s₂ ∶ s ∶ C
                                → Γ , ⟨ 2 , B ⟩ ⊢ u₂ ∶ u ∶ C
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
    ★ⁿ_ {𝐭 = t₂ ∷ t ∷ []}-}


-- --------------------------------------------------------------------------
--
-- Notation for typed terms at level 4


{-𝝀⁴_ : ∀{t₃ t₂ t A B Γ}
    → Γ , ⟨ 3 , A ⟩ ⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ ⊢ 𝜆³ t₃ ∶ 𝜆² t₂ ∶ 𝜆 t ∶ (A ⊃ B)
𝝀⁴_ {t₃} {t₂} {t} =
    𝝀ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}

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
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ∨ B)    → Γ , ⟨ 3 , A ⟩ ⊢ s₃ ∶ s₂ ∶ s ∶ C
                                     → Γ , ⟨ 3 , B ⟩ ⊢ u₃ ∶ u₂ ∶ u ∶ C
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
    ★ⁿ_ {𝐭 = t₃ ∷ t₂ ∷ t ∷ []}-}


-- --------------------------------------------------------------------------
--
-- Quotation


quot : ∀{n Γ} {𝐭 : Tms (nat Γ) n} {A}
    → Γ ⊢ 𝐭 ∶ⁿ A
    → Tm (nat Γ)
quot (𝒗 i)                 = 𝑣 fin i
quot {n} (𝝀ⁿ 𝒟)            = 𝜆[ suc n ] quot 𝒟
quot {n} (𝒟₀ ∙ⁿ 𝒟₁)        = quot 𝒟₀ ∘[ suc n ] quot 𝒟₁
quot {n} 𝒑ⁿ⟨ 𝒟₀ , 𝒟₁ ⟩     = 𝑝[ suc n ]⟨ quot 𝒟₀ , quot 𝒟₁ ⟩
quot {n} (𝝅₀ⁿ 𝒟)           = 𝜋₀[ suc n ] quot 𝒟
quot {n} (𝝅₁ⁿ 𝒟)           = 𝜋₁[ suc n ] quot 𝒟
quot {n} (𝜾₀ⁿ 𝒟)           = 𝜄₀[ suc n ] quot 𝒟
quot {n} (𝜾₁ⁿ 𝒟)           = 𝜄₁[ suc n ] quot 𝒟
quot {n} 𝒄ⁿ[ 𝒟 ▷ 𝒟₁ ∣ 𝒟₂ ] = 𝑐[ suc n ][ quot 𝒟 ▷ quot 𝒟₁ ∣ quot 𝒟₂ ]
quot {n} (⬆ⁿ 𝒟)            = ⇑[ suc n ] quot 𝒟
quot {n} (⬇ⁿ 𝒟)            = ⇓[ suc n ] quot 𝒟
quot {n} (★ⁿ 𝒟)            = ☆[ suc n ] quot 𝒟


-- --------------------------------------------------------------------------
--
-- Internalisation (theorem 1, p. 29 [1]; lemma 5.4, pp. 9–10 [2])


-- A , A₂ , … , Aₘ ⇒
--   x ∶ A , x₂ ∶ A₂ , … , xₘ ∶ Aₘ
prefix-each : Cx → Cx
prefix-each ∅               = ∅
prefix-each (Γ , ⟨ n , A ⟩) = prefix-each Γ , ⟨ suc n , A ⟩


-- yₙ ∶ yₙ₋₁ ∶ … ∶ y ∶ A⁰ₖ ∈ A , A₂ , … , Aₘ ⇒
--   xₖ ∶ yₙ ∶ yₙ₋₁ ∶ … ∶ y ∶ A⁰ₖ ∈ x ∶ A, x₂ ∶ A₂ , … , xₘ ∶ Aₘ
int∈ : ∀{Γ n A}
    → ⟨ n , A ⟩ ∈ Γ
    → ⟨ suc n , A ⟩ ∈ prefix-each Γ
int∈ 𝐙     = 𝐙
int∈ (𝐒 i) = 𝐒 (int∈ i)


same-nat : (Γ : Cx)
    → nat (prefix-each Γ) ≡ nat Γ
same-nat ∅       = refl
same-nat (Γ , x) = cong suc (same-nat Γ)

same-tms : ∀{Γ n}
    → Tms (nat Γ) n
    → Tms (nat (prefix-each Γ)) n
same-tms {Γ} tms rewrite same-nat Γ = tms

same-over-map : ∀{Γ n}
    → (f : ∀{m} → ℕ → Tm m → Tm m)
    → (𝐭 : Tms (nat Γ) n)
    → same-tms (map# f 𝐭) ≡ map# f (same-tms 𝐭)
same-over-map {Γ} f 𝐭
    rewrite same-nat Γ = refl

𝜆-same-over-map : ∀{Γ n}
    → (f : ∀{m} → ℕ → Tm (suc m) → Tm m)
    → (𝐭 : Tms (suc (nat Γ)) n)    → (A : Ty)
    → same-tms (map# f 𝐭) ≡ map# f (same-tms {Γ = Γ , ⟨ n , A ⟩} {n} 𝐭)
𝜆-same-over-map {Γ} f 𝐭 A
    rewrite same-nat Γ = refl

same-over-map2 : ∀{Γ n}
    → (f : ∀{m} → ℕ → Tm m → Tm m → Tm m)
    → (𝐭 𝐬 : Tms (nat Γ) n)
    → same-tms (map2# f 𝐭 𝐬) ≡ map2# f (same-tms 𝐭) (same-tms 𝐬)
same-over-map2 {Γ} f 𝐭 𝐬
    rewrite same-nat Γ = refl

same-over-map3 : ∀{Γ n}
    → (f : ∀{m} → ℕ → Tm m → Tm m → Tm m → Tm m)
    → (𝐭 𝐬 𝐮 : Tms (nat Γ) n)
    → same-tms (map3# f 𝐭 𝐬 𝐮) ≡ map3# f (same-tms 𝐭) (same-tms 𝐬) (same-tms 𝐮)
same-over-map3 {Γ} f 𝐭 𝐬 𝐮
    rewrite same-nat Γ = refl

𝑐-same-over-map3 : ∀{Γ n}
    → (f : ∀{m} → ℕ → Tm m → Tm (suc m) → Tm (suc m) → Tm m)
    → (𝐭 : Tms (nat Γ) n)    → (𝐬 𝐮 : Tms (suc (nat Γ)) n)    → (A B : Ty)
    → same-tms (map3# f 𝐭 𝐬 𝐮) ≡ map3# f (same-tms 𝐭) (same-tms {Γ = Γ , ⟨ n , A ⟩} 𝐬) (same-tms {Γ = Γ , ⟨ n , B ⟩} 𝐮)
𝑐-same-over-map3 {Γ} f 𝐭 𝐬 𝐮 A B
    rewrite same-nat Γ = refl


-- A , A₂ , … , Aₘ ⊢ B ⇒
--   x ∶ A , x₂ ∶ A₂ , … xₘ ∶ Aₘ ⊢ t (x , x₂ , … , xₘ) ∶ B
int⊢ : ∀{Γ n} {𝐭 : Tms (nat Γ) n} {B}
    → (𝒟 : Γ ⊢ 𝐭 ∶ⁿ B)
    → prefix-each Γ ⊢ same-tms (quot 𝒟 ∷ 𝐭) ∶ⁿ B

int⊢ (𝒗 i) = {!𝒗 int∈ i!}

int⊢ {Γ} {n} (𝝀ⁿ_ {𝐭} {A} 𝒟)
    rewrite 𝜆-same-over-map 𝜆[_]_ (quot 𝒟 ∷ 𝐭) A =
        𝝀ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} {!int⊢ 𝒟!}

int⊢ (_∙ⁿ_ {𝐭} {𝐬} 𝒟 𝒞)
    rewrite same-over-map2 (λ n t s → t ∘[ n ] s) (quot 𝒟 ∷ 𝐭) (quot 𝒞 ∷ 𝐬) =
        _∙ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} {𝐬 = same-tms (quot 𝒞 ∷ 𝐬)} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝒑ⁿ⟨_,_⟩ {𝐭} {𝐬} 𝒟 𝒞)
    rewrite same-over-map2 𝑝[_]⟨_,_⟩ (quot 𝒟 ∷ 𝐭) (quot 𝒞 ∷ 𝐬) =
        𝒑ⁿ⟨_,_⟩ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} {same-tms (quot 𝒞 ∷ 𝐬)} (int⊢ 𝒟) (int⊢ 𝒞)

int⊢ (𝝅₀ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map 𝜋₀[_]_ (quot 𝒟 ∷ 𝐭) =
        𝝅₀ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ (𝝅₁ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map 𝜋₁[_]_ (quot 𝒟 ∷ 𝐭) =
        𝝅₁ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ (𝜾₀ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map 𝜄₀[_]_ (quot 𝒟 ∷ 𝐭) =
        𝜾₀ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ (𝜾₁ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map 𝜄₁[_]_ (quot 𝒟 ∷ 𝐭) =
        𝜾₁ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ {Γ} {n} (𝒄ⁿ[_▷_∣_] {𝐭} {𝐬} {𝐮} {A} {B} 𝒟 𝒞 ℰ)
    rewrite 𝑐-same-over-map3 𝑐[_][_▷_∣_] (quot 𝒟 ∷ 𝐭) (quot 𝒞 ∷ 𝐬) (quot ℰ ∷ 𝐮) A B =
        𝒄ⁿ[_▷_∣_] {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} {same-tms (quot 𝒞 ∷ 𝐬)} {same-tms (quot ℰ ∷ 𝐮)} (int⊢ 𝒟) {!int⊢ 𝒞!} {!int⊢ ℰ!}

int⊢ (⬆ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map ⇑[_]_ (quot 𝒟 ∷ 𝐭) =
        ⬆ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ (⬇ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map ⇓[_]_ (quot 𝒟 ∷ 𝐭) =
        ⬇ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)

int⊢ (★ⁿ_ {𝐭} 𝒟)
    rewrite same-over-map ☆[_]_ (quot 𝒟 ∷ 𝐭) =
        ★ⁿ_ {𝐭 = same-tms (quot 𝒟 ∷ 𝐭)} (int⊢ 𝒟)


-- -- --------------------------------------------------------------------------
-- --
-- -- Weakening


-- wk∈ : ∀{x A Δ}
--     → (Γ : Cx)    → A ∈[ x ] (∅ „ Γ)
--     → A ∈[ x ] (Δ „ Γ)
-- wk∈ ∅       ()
-- wk∈ (Γ , A) 𝐙     = 𝐙
-- wk∈ (Γ , A) (𝐒 i) = 𝐒 (wk∈ Γ i)


-- wk⊢ : ∀{A Δ}
--     → (Γ : Cx)    → ∅ „ Γ ⊢ A
--     → Δ „ Γ ⊢ A

-- wk⊢ Γ (𝒗 i)               = 𝒗 wk∈ Γ i
-- wk⊢ Γ (𝝀ⁿ_ {n} {𝐭} {A} 𝒟) = 𝝀ⁿ_ {𝐭 = 𝐭} (wk⊢ (Γ , ⟨ n , A ⟩) 𝒟)

-- wk⊢ Γ (_∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
--     _∙ⁿ_ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

-- wk⊢ Γ (𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} 𝒟 𝒞) =
--     𝒑ⁿ⟨_,_⟩ {𝐭 = 𝐭} {𝐬 = 𝐬} (wk⊢ Γ 𝒟) (wk⊢ Γ 𝒞)

-- wk⊢ Γ (𝝅₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
-- wk⊢ Γ (𝝅₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝝅₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
-- wk⊢ Γ (𝜾₀ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₀ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
-- wk⊢ Γ (𝜾₁ⁿ_ {𝐭 = 𝐭} 𝒟) = 𝜾₁ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)

-- wk⊢ Γ (𝒄ⁿ[_▷_∣_] {n} {𝐭} {𝐬} {𝐮} {A} {B} 𝒟 𝒞 ℰ) =
--     𝒄ⁿ[_▷_∣_] {𝐭 = 𝐭} {𝐬 = 𝐬}
--                       {𝐮 = 𝐮} (wk⊢ Γ 𝒟) (wk⊢ (Γ , ⟨ n , A ⟩) 𝒞)
--                                          (wk⊢ (Γ , ⟨ n , B ⟩) ℰ)

-- wk⊢ Γ (⬆ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬆ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
-- wk⊢ Γ (⬇ⁿ_ {𝐭 = 𝐭} 𝒟) = ⬇ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)
-- wk⊢ Γ (★ⁿ_ {𝐭 = 𝐭} 𝒟) = ★ⁿ_ {𝐭 = 𝐭} (wk⊢ Γ 𝒟)


-- -- --------------------------------------------------------------------------
-- --
-- -- Constructive necessitation (corollary 5.5, p. 10 [2])


-- nec : ∀{A}
--     → (𝒟 : ∅ ⊢ A)
--     → ⊩ quot 𝒟 ∶ A
-- nec 𝒟 = wk⊢ ∅ (int⊢ 𝒟)


-- --------------------------------------------------------------------------
--
-- Examples


-- Some theorems of propositional logic
module PL where
  I : ∀{Γ A}
      → Γ ⊢ A ⊃ A
  I = 𝝀 𝒗 𝟎

  K : ∀{Γ A B}
      → Γ ⊢ A ⊃ B ⊃ A
  K = 𝝀 𝝀 𝒗 𝟏

  S : ∀{Γ A B C}
      → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = 𝝀 𝝀 𝝀 (𝒗 𝟐 ∙ 𝒗 𝟎) ∙ (𝒗 𝟏 ∙ 𝒗 𝟎)

  X1 : ∀{Γ A B}
      → Γ ⊢ A ⊃ B ⊃ A ∧ B
  X1 = 𝝀 𝝀 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩


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


postulate
  push : ∀{Γ} {t : Tm 0} {A}
      → ∅ ⊢ t ∵ A
      → Γ ⊢ t ∶ A


-- Some theorems of modal logic S4
module S4 where
  -- □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K : ∀{Γ A B f x}
      → Γ ⊢ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
  K = 𝝀 𝝀 {!𝒗 𝟏!} ∙ {!𝒗 𝟎!} -- 𝝀 𝝀 {!𝒗 𝟏 ∙² 𝒗 𝟎!} -- (𝒗 𝟏 ∙² 𝒗 𝟎)

  -- □ A ⊃ A
  T : ∀{Γ A x}
      → Γ ⊢ x ∶ A ⊃ A
  T = 𝝀 ⬇ 𝒗 𝟎

  -- □ A ⊃ □ □ A
  #4 : ∀{Γ A x}
      → Γ ⊢ x ∶ A ⊃ ! x ∶ x ∶ A
  #4 = 𝝀 ⬆ 𝒗 𝟎

  -- □ A ⊃ □ B ⊃ □ □ (A ∧ B)
  X1 : ∀{Γ A B x y}
      → Γ ⊢ x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
  X1 = 𝝀 𝝀 ⬆ {!!} -- 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

  -- □ A ⊃ □ B ⊃ □ (A ∧ B)
  X2 : ∀{Γ A B x y}
      → Γ ⊢ x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
  X2 = 𝝀 𝝀 {!!} -- 𝒑²⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩

  -- □ A ∧ □ B ⊃ □ □ (A ∧ B)
  X3 : ∀{Γ A B x y}
      → Γ ⊢ x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
  X3 = 𝝀 ⬆ {!!} -- 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩

  -- □ A ∧ □ B ⊃ □ (A ∧ B)
  X4 : ∀{Γ A B x y}
      → Γ ⊢ x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
  X4 = 𝝀 {!!} -- 𝒑²⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩


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
--       → ⊩ 𝜆² ⇓² ⇑² 𝑣 0 ∶ 𝜆 ⇓ ⇑ 𝑣 0 ∶ (x ∶ A ⊃ x ∶ A)
--   E2 = 𝝀³ ⬇³ ⬆³ 𝒗 𝟎

--   E2a : ∀{x A}
--       → ⊩ 𝜆² 𝑣 0 ∶ 𝜆 𝑣 0 ∶ (x ∶ A ⊃ x ∶ A)
--   E2a = 𝝀³ 𝒗 𝟎


-- -- --------------------------------------------------------------------------
-- --
-- -- Additional examples


-- -- De Morgan’s laws
-- module DeMorgan where
--   -- (A ⊃ ⊥) ∧ (B ⊃ ⊥) ⫗ (A ∨ B) ⊃ ⊥
--   L1 : ∀{A B}
--       → ⊩ ¬ A ∧ ¬ B ⫗ ¬ (A ∨ B)
--   L1 = 𝒑⟨ 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ]
--         , 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩ ⟩

--   -- (A ⊃ ⊥) ∨ (B ⊃ ⊥) ⊃ (A ⊃ ⊥) ∧ B
--   L2 : ∀{A B}
--       → ⊩ ¬ A ∨ ¬ B ⊃ ¬ (A ∧ B)
--   L2 = 𝝀 𝝀 𝒄[ 𝒗 𝟏 ▷ 𝒗 𝟎 ∙ 𝝅₀ 𝒗 𝟏 ∣ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟏 ]


-- -- Explosions and contradictions
-- module ExploCon where
--   X1 : ∀{A}
--       → ⊩ ⊥ ⊃ A
--   X1 = 𝝀 ★ 𝒗 𝟎

--   -- □ (⊥ ⊃ A)
--   X1² : ∀{A}
--       → ⊩ 𝜆 ☆ 𝑣 0 ∶ (⊥ ⊃ A)
--   X1² = nec X1

--   -- □ ⊥ ⊃ □ A
--   X2 : ∀{x A}
--       → ⊩ x ∶ ⊥ ⊃ ☆ x ∶ A
--   X2 = 𝝀 ★² 𝒗 𝟎

--   X3 : ∀{A}
--       → ⊩ ¬ A ⊃ A ⊃ ⊥
--   X3 = 𝝀 𝝀 𝒗 𝟏 ∙ 𝒗 𝟎

--   -- □ (¬ A) ⊃ □ A ⊃ □ ⊥
--   X4 : ∀{x y A}
--       → ⊩ x ∶ (¬ A) ⊃ y ∶ A ⊃ x ∘ y ∶ ⊥
--   X4 = 𝝀 𝝀 𝒗 𝟏 ∙² 𝒗 𝟎

--   -- □ (¬ A) ⊃ □ A ⊃ □ □ ⊥
--   X5 : ∀{x y A}
--       → ⊩ x ∶ (¬ A) ⊃ y ∶ A ⊃ ! (x ∘ y) ∶ x ∘ y ∶ ⊥
--   X5 = 𝝀 𝝀 ⬆ 𝒗 𝟏 ∙² 𝒗 𝟎


-- -- --------------------------------------------------------------------------
-- --
-- -- Further examples


-- module Idempotence where
--   ⊃-idem : ∀{A}
--       → ⊩ A ⊃ A ⫗ ⊤
--   ⊃-idem = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
--             , 𝝀 𝝀 𝒗 𝟎 ⟩

--   ∧-idem : ∀{A}
--       → ⊩ A ∧ A ⫗ A
--   ∧-idem = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
--             , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝒗 𝟎 ⟩ ⟩

--   ∨-idem : ∀{A}
--       → ⊩ A ∨ A ⫗ A
--   ∨-idem = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ 𝒗 𝟎 ]
--             , 𝝀 𝜾₀ 𝒗 𝟎 ⟩


-- module Commutativity where
--   ∧-comm : ∀{A B}
--       → ⊩ A ∧ B ⫗ B ∧ A
--   ∧-comm = 𝒑⟨ 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩
--             , 𝝀 𝒑⟨ 𝝅₁ 𝒗 𝟎 , 𝝅₀ 𝒗 𝟎 ⟩ ⟩

--   ∨-comm : ∀{A B}
--       → ⊩ A ∨ B ⫗ B ∨ A
--   ∨-comm = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ]
--             , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₀ 𝒗 𝟎 ] ⟩


-- module Associativity where
--   ∧-assoc : ∀{A B C}
--       → ⊩ A ∧ (B ∧ C) ⫗ (A ∧ B) ∧ C
--   ∧-assoc = 𝒑⟨ 𝝀 𝒑⟨ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝝅₀ 𝝅₁ 𝒗 𝟎 ⟩ , 𝝅₁ 𝝅₁ 𝒗 𝟎 ⟩
--              , 𝝀 𝒑⟨ 𝝅₀ 𝝅₀ 𝒗 𝟎 , 𝒑⟨ 𝝅₁ 𝝅₀ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟎 ⟩ ⟩ ⟩

--   ∨-assoc : ∀{A B C}
--       → ⊩ A ∨ (B ∨ C) ⫗ (A ∨ B) ∨ C
--   ∨-assoc = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝜾₁ 𝒗 𝟎 ∣ 𝜾₁ 𝒗 𝟎 ] ]
--              , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒄[ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝜾₀ 𝒗 𝟎 ] ∣ 𝜾₁ 𝜾₁ 𝒗 𝟎 ] ⟩


-- module Distributivity where
--   ⊃-dist-∧ : ∀{A B C}
--       → ⊩ A ⊃ (B ∧ C) ⫗ (A ⊃ B) ∧ (A ⊃ C)
--   ⊃-dist-∧ = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝝅₀ (𝒗 𝟏 ∙ 𝒗 𝟎) , 𝝀 𝝅₁ (𝒗 𝟏 ∙ 𝒗 𝟎) ⟩
--               , 𝝀 𝝀 𝒑⟨ 𝝅₀ 𝒗 𝟏 ∙ 𝒗 𝟎 , 𝝅₁ 𝒗 𝟏 ∙ 𝒗 𝟎 ⟩ ⟩

--   ∧-dist-∨ : ∀{A B C}
--       → ⊩ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
--   ∧-dist-∨ = 𝒑⟨ 𝝀 𝒄[ 𝝅₁ 𝒗 𝟎 ▷ 𝜾₀ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ∣ 𝜾₁ 𝒑⟨ 𝝅₀ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ]
--               , 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₀ 𝝅₁ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ] ⟩

--   ∨-dist-∧ : ∀{A B C}
--       → ⊩ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
--   ∨-dist-∧ = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒑⟨ 𝜾₀ 𝒗 𝟎 , 𝜾₀ 𝒗 𝟎 ⟩ ∣ 𝒑⟨ 𝜾₁ 𝝅₀ 𝒗 𝟎 , 𝜾₁ 𝝅₁ 𝒗 𝟎 ⟩ ]
--               , 𝝀 𝒄[ 𝝅₀ 𝒗 𝟎 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝒄[ 𝝅₁ 𝒗 𝟏 ▷ 𝜾₀ 𝒗 𝟎 ∣ 𝜾₁ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ] ] ⟩


-- module Untitled where
--   ⊃-law : ∀{A B C}
--       → ⊩ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
--   ⊃-law = 𝝀 𝝀 𝝀 𝒗 𝟏 ∙ (𝒗 𝟐 ∙ 𝒗 𝟎)

--   ⊃-∧-law : ∀{A B C}
--       → ⊩ A ⊃ B ⊃ C ⫗ (A ∧ B) ⊃ C
--   ⊃-∧-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟏 ∙ 𝝅₀ 𝒗 𝟎 ∙ 𝝅₁ 𝒗 𝟎
--              , 𝝀 𝝀 𝝀 𝒗 𝟐 ∙ 𝒑⟨ 𝒗 𝟏 , 𝒗 𝟎 ⟩ ⟩

--   ∨-⊃-∧-law : ∀{A B C}
--       → ⊩ (A ∨ B) ⊃ C ⫗ (A ⊃ C) ∧ (B ⊃ C)
--   ∨-⊃-∧-law = 𝒑⟨ 𝝀 𝒑⟨ 𝝀 𝒗 𝟏 ∙ 𝜾₀ 𝒗 𝟎 , 𝝀 𝒗 𝟏 ∙ 𝜾₁ 𝒗 𝟎 ⟩
--                , 𝝀 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝝅₀ 𝒗 𝟐 ∙ 𝒗 𝟎 ∣ 𝝅₁ 𝒗 𝟐 ∙ 𝒗 𝟎 ] ⟩


-- module Trivial where
--   ⊃-⊤-law : ∀{A}
--       → ⊩ A ⊃ ⊤ ⫗ ⊤
--   ⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
--               , 𝝀 𝝀 𝒗 𝟏 ⟩

--   ⊤-⊃-law : ∀{A}
--       → ⊩ ⊤ ⊃ A ⫗ A
--   ⊤-⊃-law = 𝒑⟨ 𝝀 𝒗 𝟎 ∙ (𝝀 𝒗 𝟎)
--               , 𝝀 𝝀 𝒗 𝟏 ⟩

--   ⊥-⊃-⊤-law : ∀{A}
--       → ⊩ ⊥ ⊃ A ⫗ ⊤
--   ⊥-⊃-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
--                  , 𝝀 𝝀 ★ 𝒗 𝟎 ⟩

--   ∧-⊥-law : ∀{A}
--       → ⊩ A ∧ ⊥ ⫗ ⊥
--   ∧-⊥-law = 𝒑⟨ 𝝀 𝝅₁ 𝒗 𝟎
--                 , 𝝀 ★ 𝒗 𝟎 ⟩

--   ∨-⊥-law : ∀{A}
--       → ⊩ A ∨ ⊥ ⫗ A
--   ∨-⊥-law = 𝒑⟨ 𝝀 𝒄[ 𝒗 𝟎 ▷ 𝒗 𝟎 ∣ ★ 𝒗 𝟎 ]
--                 , 𝝀 𝜾₀ 𝒗 𝟎 ⟩

--   ∧-⊤-law : ∀{A}
--       → ⊩ A ∧ ⊤ ⫗ A
--   ∧-⊤-law = 𝒑⟨ 𝝀 𝝅₀ 𝒗 𝟎
--                 , 𝝀 𝒑⟨ 𝒗 𝟎 , 𝝀 𝒗 𝟎 ⟩ ⟩

--   ∨-⊤-law : ∀{A}
--       → ⊩ A ∨ ⊤ ⫗ ⊤
--   ∨-⊤-law = 𝒑⟨ 𝝀 𝝀 𝒗 𝟎
--                 , 𝝀 𝜾₁ 𝒗 𝟎 ⟩
