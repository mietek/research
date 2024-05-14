{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Work in progress.

For easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") ("N" "ℕ")
     ("v" "𝑣") ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("pi0" "𝜋₀") ("pi02" "𝜋₀²") ("pi03" "𝜋₀³") ("pi0n" "𝜋₀ⁿ")
     ("pi1" "𝜋₁") ("pi12" "𝜋₁²") ("pi13" "𝜋₁³") ("pi1n" "𝜋₁ⁿ")
     ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ")
     ("mv" "𝒗") ("ml" "𝝀") ("ml2" "𝝀²") ("ml3" "𝝀³") ("ml4" "𝝀⁴") ("mln" "𝝀ⁿ")
     ("mo" "∙") ("mo2" "∙²") ("mo3" "∙³") ("mo4" "∙⁴") ("mon" "∙ⁿ")
     ("mp" "𝒑") ("mp2" "𝒑²") ("mp3" "𝒑³") ("mp4" "𝒑⁴") ("mpn" "𝒑ⁿ")
     ("mpi0" "𝝅₀") ("mpi02" "𝝅₀²") ("mpi03" "𝝅₀³") ("mpi04" "𝝅₀⁴") ("mpi0n" "𝝅₀ⁿ")
     ("mpi1" "𝝅₁") ("mpi12" "𝝅₁²") ("mpi13" "𝝅₁³") ("mpi14" "𝝅₁⁴") ("mpi1n" "𝝅₁ⁿ")
     ("mu" "⬆") ("mu2" "⬆²") ("mu3" "⬆³") ("mu4" "⬆⁴") ("mun" "⬆ⁿ")
     ("md" "⬇") ("md2" "⬇²") ("md3" "⬇³") ("md4" "⬇⁴") ("mdn" "⬇ⁿ")
     ("mS" "𝐒") ("mZ" "𝐙")
     ("m0" "𝟎") ("m1" "𝟏") ("m2" "𝟐") ("m3" "𝟑") ("m4" "𝟒")
     ("m5" "𝟓") ("m6" "𝟔") ("m7" "𝟕") ("m8" "𝟖") ("m9" "𝟗")
     ("s" "𝐬") ("t" "𝐭") ("x" "𝐱") ("y" "𝐲"))))

-}


module A201602.Try15 where

open import Data.Nat
  using (ℕ ; zero ; suc)

open import Data.Product
  using (Σ ; _×_)
  renaming (_,_ to ⟨_,_⟩ ; proj₁ to proj₀ ; proj₂ to proj₁)

open import Data.Vec
  using (Vec ; [] ; _∷_ ; replicate)

{-infixl 9 !_
infixl 9 𝑣_ 𝒗_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₀³_ 𝝅₀_ 𝝅₀²_ 𝝅₀³_ 𝝅₀⁴_ 𝝅₀ⁿ_
infixl 8 𝜋₁_ 𝜋₁²_ 𝜋₁³_ 𝝅₁_ 𝝅₁²_ 𝝅₁³_ 𝝅₁⁴_ 𝝅₁ⁿ_
infixl 7 _∘_ _∘²_ _∘³_ _∙_ _∙²_ _∙³_ _∙⁴_ _∙ⁿ_
infixr 6 ⇑_ ⇑²_ ⇑³_ ⬆_ ⬆²_ ⬆³_ ⬆⁴_ ⬆ⁿ_
infixr 6 ⇓_ ⇓²_ ⇓³_ ⬇_ ⬇²_ ⬇³_ ⬇⁴_ ⬇ⁿ_
infixr 5 𝜆_ 𝜆²_ 𝜆³_ 𝝀_ 𝝀²_ 𝝀³_ 𝝀⁴_ 𝝀ⁿ_
infixr 4 _∶_
infixr 3 ¬_
infixl 2 _∧_
infixl 2 _,_
infixr 1 _⊃_ _⫗_
infixr 0 _⊢_ ⊩_-}


-- --------------------------------------------------------------------------
--
-- Untyped syntax


-- Variables
Var : Set
Var = ℕ


-- Term constructors
data Tm : Set where
  -- Variable
  𝑣_ : Var → Tm

  -- Abstraction (⊃I) at level n
  𝜆[_]_ : ℕ → Tm → Tm

  -- Application (⊃E) at level n
  _∘[_]_ : Tm → ℕ → Tm → Tm

  -- Pairing (∧I) at level n
  𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm

  -- 0th projection (∧E₀) at level n
  𝜋₀[_]_ : ℕ → Tm → Tm

  -- 1st projection (∧E₁) at level n
  𝜋₁[_]_ : ℕ → Tm → Tm

  -- Artëmov’s “proof checker”
  !_ : Tm → Tm

  -- Reification at level n
  ⇑[_]_ : ℕ → Tm → Tm

  -- Reflection at level n
  ⇓[_]_ : ℕ → Tm → Tm


mutual
  -- Type constructors
  data Ty : Set where
    -- Falsehood
    ⊥ : Ty

    -- Implication
    _⊃_ : Ty → Ty → Ty

    -- Conjunction
    _∧_ : Ty → Ty → Ty

    -- Type assertion
    α_ : TyA → Ty


  -- Type assertion constructor
  data TyA : Set where
    -- Explicit provability
    -- _∋_ : ∀{Γ} → (A : Ty) → (t : Tm Γ) → TyA


-- Hypotheses
Hyp : Set
Hyp = ℕ × Ty


-- Contexts
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Hyp → Cx


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
