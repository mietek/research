{-

An implementation of the Alt-Artëmov system λ∞
==============================================

Work in progress.

For  easy editing with Emacs agda-mode, add to your .emacs file:

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("ii" "⫗") ("e" "⊢") ("ee" "⊩") ("n" "¬") ("N" "ℕ")
     ("." "·") (":" "∶") (":" "∴") (":" "∵") ("::" "∷")
     ("Mv" "M𝑣") ("v" "𝑣") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("Ml" "M𝜆") ("l" "𝜆") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("Mo" "M∘") ("o" "∘") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("Mp" "M𝑝") ("p" "𝑝") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("M1" "M𝜋₀") ("1" "𝜋₀") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("M2" "M𝜋₁") ("2" "𝜋₁") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("Mu" "M⇑") ("u" "⇑") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("Md" "M⇓") ("d" "⇓") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ")
     ("M-" "M⁻") ("M+" "M⁺"))))

-}


module Try13 where

open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ) renaming (_,_ to ⟨_,_⟩)

infixl 9 !_ 𝑣_
infixl 8 𝜋₀_ 𝜋₀²_ 𝜋₀ⁿ_ 𝜋₁_ 𝜋₁²_ 𝜋₁ⁿ_
infixl 7 _∘_ _∘²_ _∘ⁿ_
infixr 6 ⇑_ ⇑²_ ⇑ⁿ_ ⇓_ ⇓²_ ⇓ⁿ_
infixr 5 𝜆_·_ 𝜆²_·_ 𝜆ⁿ_·_
infixr 4 _∶_
infixr 3 ¬_
infixr 2 _‘_
infixl 2 _,_ _∧_
infixr 1 _⊃_ _⊃⊂_
infixr 0 _⊢_∷_ ⊩_ ⊩_∷_ ⊩_∷_∷_


-- --------------------------------------------------------------------------
--
-- Untyped syntax


Var : Set
Var = ℕ


-- Type and term constructors

mutual
  data Ty : Set where
    -- Falsehood
    ⊥ : Ty

    -- Implication
    _⊃_ : Ty → Ty → Ty

    -- Conjunction
    _∧_ : Ty → Ty → Ty

    -- Explicit provability
    _∶_ : Tm → Ty → Ty


  data Tm : Set where
    -- Variable
    𝑣_ : Var → Tm

    -- Abstraction (⊃I)
    𝜆[_]_·_ : ℕ → Var → Tm → Tm

    -- Application (⊃E)
    _∘[_]_ : Tm → ℕ → Tm → Tm

    -- Pairing (∧I)
    𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm

    -- First projection (∧E₀)
    𝜋₀[_]_ : ℕ → Tm → Tm

    -- Second projection (∧E₁)
    𝜋₁[_]_ : ℕ → Tm → Tm

    -- Artëmov’s “proof checker”
    !_ : Tm → Tm

    -- Reification
    ⇑[_]_ : ℕ → Tm → Tm

    -- Reflection
    ⇓[_]_ : ℕ → Tm → Tm


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
_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 1 and 2 term constructors


𝜆_·_ : Var → Tm → Tm
𝜆 x · t = 𝜆[ 1 ] x · t

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘[ 1 ] s

𝑝⟨_,_⟩ : Tm → Tm → Tm
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝜋₀_ : Tm → Tm
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₁_ : Tm → Tm
𝜋₁ t = 𝜋₁[ 1 ] t

⇑_ : Tm → Tm
⇑ t = ⇑[ 1 ] t

⇓_ : Tm → Tm
⇓ t = ⇓[ 1 ] t


𝜆²_·_ : Var → Tm → Tm
𝜆² x₂ · t₂ = 𝜆[ 2 ] x₂ · t₂

_∘²_ : Tm → Tm → Tm
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝²⟨_,_⟩ : Tm → Tm → Tm
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀²_ : Tm → Tm
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁²_ : Tm → Tm
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

⇑²_ : Tm → Tm
⇑² t₂ = ⇑[ 2 ] t₂

⇓²_ : Tm → Tm
⇓² t₂ = ⇓[ 2 ] t₂


-- --------------------------------------------------------------------------
--
-- Generic vectors


data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _‘_ : ∀{n} → X → Vec X n → Vec X (suc n)


append : ∀{n} {X : Set}
        → Vec X n → X → Vec X (suc n)
append []       y = y ‘ []
append (x ‘ xs) y = x ‘ append xs y

foldr : ∀{n} {X : Set} (Y : ℕ → Set)
      → (∀{k} → X → Y k → Y (suc k)) → Y zero → Vec X n → Y n
foldr Y f y₀ []       = y₀
foldr Y f y₀ (x ‘ xs) = f x (foldr Y f y₀ xs)

ixMap : ∀{n} {X Y : Set}
      → (ℕ → X → Y) → Vec X n → Vec Y n
ixMap {zero}  f []       = []
ixMap {suc n} f (x ‘ xs) = f (suc n) x ‘ ixMap f xs

ixZipWith : ∀{n} {X Y Z : Set}
          → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
ixZipWith {zero}  f []       []       = []
ixZipWith {suc n} f (x ‘ xs) (y ‘ ys) = f (suc n) x y ‘ ixZipWith f xs ys


map : ∀{n} {X Y : Set}
    → (X → Y) → Vec X n → Vec Y n
map f = ixMap (λ _ x → f x)

zip : ∀{n} {X Y Z : Set}
    → (X → Y → Z) → Vec X n → Vec Y n → Vec Z n
zip f = ixZipWith (λ _ x y → f x y)


[_] : {X : Set} → X → Vec X 1
[ x ] = x ‘ []

[_∷_] : {X : Set} → X → X → Vec X 2
[ x₂ ∷ x ] = x₂ ‘ x ‘ []


-- --------------------------------------------------------------------------
--
-- Vector notation for level n term constructors


Vars : ℕ → Set
Vars = Vec Var

Tms : ℕ → Set
Tms = Vec Tm


𝜆ⁿ_·_ : ∀{n} → Vars n → Tms n → Tms n
𝜆ⁿ_·_ = ixZipWith 𝜆[_]_·_

_∘ⁿ_ : ∀{n} → Tms n → Tms n → Tms n
_∘ⁿ_ = ixZipWith (λ n t s → t ∘[ n ] s)

𝑝ⁿ⟨_,_⟩ : ∀{n} → Tms n → Tms n → Tms n
𝑝ⁿ⟨_,_⟩ = ixZipWith 𝑝[_]⟨_,_⟩

𝜋₀ⁿ_ : ∀{n} → Tms n → Tms n
𝜋₀ⁿ_ = ixMap 𝜋₀[_]_

𝜋₁ⁿ_ : ∀{n} → Tms n → Tms n
𝜋₁ⁿ_ = ixMap 𝜋₁[_]_

⇑ⁿ_ : ∀{n} → Tms n → Tms n
⇑ⁿ_ = ixMap ⇑[_]_

⇓ⁿ_ : ∀{n} → Tms n → Tms n
⇓ⁿ_ = ixMap ⇓[_]_


-- --------------------------------------------------------------------------
--
-- Typing contexts


record Hyp (n : ℕ) : Set where
  constructor ⟨_∷_⟩
  field
    tms : Tms n
    ty  : Ty


data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{m n} → Cx m → Hyp n → Cx (suc m)


data _∈_  : ∀{m n} → Hyp n → Cx m → Set where
  Z  : ∀{m n} {Γ : Cx m} {A : Hyp n}
    → A ∈ (Γ , A)

  S_ : ∀{m n k} {Γ : Cx m} {A : Hyp n} {B : Hyp k}
    → A ∈ Γ
    → A ∈ (Γ , B)


-- --------------------------------------------------------------------------
--
-- Typing judgment


data _⊢_∷_ {m : ℕ} (Γ : Cx m) : ∀{n} → Tms n → Ty → Set where
  M𝑣  : ∀{A n} {ts : Tms n}
      → ⟨ ts ∷ A ⟩ ∈ Γ
      → Γ ⊢ ts ∷ A

  M𝜆  : ∀{A B n} {xs : Vars n} {ts : Tms n}
      → Γ , ⟨ map 𝑣_ xs ∷ A ⟩ ⊢ ts ∷ B
      → Γ ⊢ 𝜆ⁿ xs · ts ∷ A ⊃ B

  M∘  : ∀{A B n} {ts ss : Tms n}
      → Γ ⊢ ts ∷ A ⊃ B    → Γ ⊢ ss ∷ A
      → Γ ⊢ ts ∘ⁿ ss ∷ B

  M𝑝  : ∀{A B n} {ts ss : Tms n}
      → Γ ⊢ ts ∷ A        → Γ ⊢ ss ∷ B
      → Γ ⊢ 𝑝ⁿ⟨ ts , ss ⟩ ∷ A ∧ B

  M𝜋₀ : ∀{A B n} {ts : Tms n}
      → Γ ⊢ ts ∷ A ∧ B
      → Γ ⊢ 𝜋₀ⁿ ts ∷ A

  M𝜋₁ : ∀{A B n} {ts : Tms n}
      → Γ ⊢ ts ∷ A ∧ B
      → Γ ⊢ 𝜋₁ⁿ ts ∷ B

  M⇑  : ∀{A u n} {ts : Tms n}
      → Γ ⊢ ts ∷ u ∶ A
      → Γ ⊢ ⇑ⁿ ts ∷ ! u ∶ u ∶ A

  M⇓  : ∀{A u n} {ts : Tms n}
      → Γ ⊢ ts ∷ u ∶ A
      → Γ ⊢ ⇓ⁿ ts ∷ A

  M⁻  : ∀{A u n} {ts : Tms n}
      → Γ ⊢ ts ∷ u ∶ A
      → Γ ⊢ append ts u ∷ A

  M⁺  : ∀{A u n} {ts : Tms n}
      → Γ ⊢ append ts u ∷ A
      → Γ ⊢ ts ∷ u ∶ A


_⊢_ : ∀{m n} → Cx m → Hyp n → Set
Γ ⊢ ⟨ ts ∷ A ⟩ = Γ ⊢ ts ∷ A


-- --------------------------------------------------------------------------
--
-- Simplified notation for level 0, 1, and 2 typing judgements


⊩_ : Ty → Set
⊩ A = ∀{m} {Γ : Cx m} → Γ ⊢ [] ∷ A

⊩_∷_ : Tm → Ty → Set
⊩ t ∷ A = ∀{m} {Γ : Cx m} → Γ ⊢ [ t ] ∷ A

⊩_∷_∷_ : Tm → Tm → Ty → Set
⊩ t₂ ∷ t ∷ A = ∀{m} {Γ : Cx m} → Γ ⊢ [ t₂ ∷ t ] ∷ A


-- --------------------------------------------------------------------------
--
-- Example terms for level 0, 1, and 2 IKS combinators


-- S4: A ⊃ A
eI⁰ : ∀{A}
    → ⊩ A ⊃ A
eI⁰ = M𝜆 (M𝑣 Z)

-- S4: □(A ⊃ A)
eI¹ : ∀{A x}
    → ⊩ 𝜆 x · 𝑣 x
        ∷ A ⊃ A
eI¹ = M𝜆 (M𝑣 Z)

-- S4: □□(A ⊃ A)
eI² : ∀{A x u}
    → ⊩ 𝜆² u · 𝑣 u
        ∷ 𝜆 x · 𝑣 x
        ∷ A ⊃ A
eI² = M𝜆 (M𝑣 Z)


-- S4: A ⊃ B ⊃ A
eK⁰ : ∀{A B}
    → ⊩ A ⊃ B ⊃ A
eK⁰ = M𝜆 (M𝜆 (M𝑣 (S Z)))

-- S4: □(A ⊃ B ⊃ A)
eK¹ : ∀{A B x y}
    → ⊩ 𝜆 x · 𝜆 y · 𝑣 x
        ∷ A ⊃ B ⊃ A
eK¹ = M𝜆 (M𝜆 (M𝑣 (S Z)))

-- S4: □□(A ⊃ B ⊃ A)
eK² : ∀{A B x y u v}
    → ⊩ 𝜆² u · 𝜆² v · 𝑣 u
        ∷ 𝜆 x · 𝜆 y · 𝑣 x
        ∷ A ⊃ B ⊃ A
eK² = M𝜆 (M𝜆 (M𝑣 (S Z)))


-- S4: (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ : ∀{A B C}
    → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 (S S Z))
                         (M𝑣 Z))
                 (M∘ (M𝑣 (S Z))
                     (M𝑣 Z)))))

-- S4: □((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS¹ : ∀{A B C f g x}
    → ⊩ 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
        ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS¹ = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 (S S Z))
                         (M𝑣 Z))
                 (M∘ (M𝑣 (S Z))
                     (M𝑣 Z)))))

-- S4: □□((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
eS² : ∀{A B C f g x p q u}
    → ⊩ 𝜆² p · 𝜆² q · 𝜆² u · (𝑣 p ∘² 𝑣 u) ∘² (𝑣 q ∘² 𝑣 u)
        ∷ 𝜆 f · 𝜆 g · 𝜆 x · (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
        ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS² = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 (S S Z))
                         (M𝑣 Z))
                 (M∘ (M𝑣 (S Z))
                     (M𝑣 Z)))))


-- --------------------------------------------------------------------------
--
-- Example terms for S4 axioms


-- S4: □(A ⊃ B) ⊃ □A ⊃ □B
axK⁰ : ∀{A B f x}
     → ⊩ (f ∶ (A ⊃ B)) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK⁰ = M𝜆 (M𝜆 (M⁺ (M∘ (M⁻ (M𝑣 (S Z)))
                      (M⁻ (M𝑣 Z)))))

-- S4: □(□(A ⊃ B) ⊃ □A ⊃ □B)
axK¹ : ∀{A B f x p u}
     → ⊩ 𝜆 p · 𝜆 u · 𝑣 p ∘² 𝑣 u
         ∷ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK¹ = M𝜆 (M𝜆 (M⁺ (M∘ (M⁻ (M𝑣 (S Z)))
                      (M⁻ (M𝑣 Z)))))

-- S4: □A ⊃ A
axT⁰ : ∀{A x}
     → ⊩ x ∶ A ⊃ A
axT⁰ = M𝜆 (M⇓ (M𝑣 Z))

-- S4: □A ⊃ □□A
ax4⁰ : ∀{A x}
     → ⊩ x ∶ A ⊃ ! x ∶ x ∶ A
ax4⁰ = M𝜆 (M⇑ (M𝑣 Z))


-- --------------------------------------------------------------------------
--
-- Terms for example 1, p. 28 [1]


-- S4: □(□A ⊃ A)
e11 : ∀{A x y}
    → ⊩ 𝜆 y · ⇓ 𝑣 y
        ∷ x ∶ A ⊃ A
e11 = M𝜆 (M⇓ (M𝑣 Z))

-- S4: □(□A ⊃ □□A)
e12 : ∀{A x y}
    → ⊩ 𝜆 y · ⇑ 𝑣 y
        ∷ x ∶ A ⊃ ! x ∶ x ∶ A
e12 = M𝜆 (M⇑ (M𝑣 Z))

-- S4: □□(A ⊃ B ⊃ A ∧ B)
e13 : ∀{A B x y u v}
    → ⊩ 𝜆² u · 𝜆² v · 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∷ 𝜆 x · 𝜆 y · 𝑝⟨ 𝑣 x , 𝑣 y ⟩
        ∷ A ⊃ B ⊃ A ∧ B
e13 = M𝜆 (M𝜆 (M𝑝 (M𝑣 (S Z))
                 (M𝑣 Z)))

-- S4: □(□A ⊃ □B ⊃ □□(A ∧ B))
e14 : ∀{A B x y u v}
    → ⊩ 𝜆 u · 𝜆 v · ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∷ x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
e14 = M𝜆 (M𝜆 (M⇑ (M⁺ (M𝑝 (M⁻ (M𝑣 (S Z)))
                         (M⁻ (M𝑣 Z))))))


-- --------------------------------------------------------------------------
--
-- Additional example terms


-- S4: □(□A ⊃ □B ⊃ □(A ∧ B))
ex1 : ∀{A B x y u v}
    → ⊩ 𝜆 u · 𝜆 v · 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
        ∷ x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
ex1 = M𝜆 (M𝜆 (M⁺ (M𝑝 (M⁻ (M𝑣 (S Z)))
                     (M⁻ (M𝑣 Z)))))

-- S4: □(□A ∧ □B ⊃ □□(A ∧ B))
ex2 : ∀{A B x y u}
    → ⊩ 𝜆 u · ⇑ 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
        ∷ x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
ex2 = M𝜆 (M⇑ (M⁺ (M𝑝 (M⁻ (M𝜋₀ (M𝑣 Z)))
                     (M⁻ (M𝜋₁ (M𝑣 Z))))))

-- S4: □(□A ∧ □B ⊃ □(A ∧ B))
ex3 : ∀{A B x y u}
    → ⊩ 𝜆 u · 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
        ∷ x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
ex3 = M𝜆 (M⁺ (M𝑝 (M⁻ (M𝜋₀ (M𝑣 Z)))
                 (M⁻ (M𝜋₁ (M𝑣 Z)))))


-- --------------------------------------------------------------------------
--
-- Terms for example 2, pp. 31–32 [1]


e2 : ∀{A x₃ x₂ x₁}
   → ⊩ 𝜆² x₃ · ⇓² ⇑² 𝑣 x₃
       ∷ 𝜆 x₂ · ⇓ ⇑ 𝑣 x₂
       ∷ x₁ ∶ A ⊃ x₁ ∶ A
e2 = M𝜆 (M⇓ (M⇑ (M𝑣 Z)))

e2′ : ∀{A x₃ x₂ x₁}
    → ⊩ 𝜆² x₃ · 𝑣 x₃
        ∷ 𝜆 x₂ · 𝑣 x₂
        ∷ x₁ ∶ A ⊃ x₁ ∶ A
e2′ = M𝜆 (M𝑣 Z)


-- --------------------------------------------------------------------------
--
-- Weakening


data _≲_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≲ ∅

  keep : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
       → Γ ≲ Γ′
       → (Γ , A) ≲ (Γ′ , A)

  drop : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
       → Γ ≲ Γ′
       → Γ ≲ (Γ′ , A)


∅≲Γ : ∀{m} {Γ : Cx m} → ∅ ≲ Γ
∅≲Γ {Γ = ∅}     = base
∅≲Γ {Γ = Γ , A} = drop ∅≲Γ


Γ≲Γ : ∀{m} {Γ : Cx m} → Γ ≲ Γ
Γ≲Γ {Γ = ∅}     = base
Γ≲Γ {Γ = Γ , A} = keep Γ≲Γ


wk∈ : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
    → Γ ≲ Γ′    → A ∈ Γ
    → A ∈ Γ′
wk∈ base     ()
wk∈ (keep P) Z     = Z
wk∈ (keep P) (S i) = S wk∈ P i
wk∈ (drop P) i     = S wk∈ P i


wk⊢ : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
     → Γ ≲ Γ′    → Γ ⊢ A
     → Γ′ ⊢ A
wk⊢ P (M𝑣 i)    = M𝑣 (wk∈ P i)
wk⊢ P (M𝜆 D)    = M𝜆 (wk⊢ (keep P) D)
wk⊢ P (M∘ D D′) = M∘ (wk⊢ P D) (wk⊢ P D′)
wk⊢ P (M𝑝 D D′) = M𝑝 (wk⊢ P D) (wk⊢ P D′)
wk⊢ P (M𝜋₀ D)   = M𝜋₀ (wk⊢ P D)
wk⊢ P (M𝜋₁ D)   = M𝜋₁ (wk⊢ P D)
wk⊢ P (M⇑ D)    = M⇑ (wk⊢ P D)
wk⊢ P (M⇓ D)    = M⇓ (wk⊢ P D)
wk⊢ P (M⁻ D)    = M⁻ (wk⊢ P D)
wk⊢ P (M⁺ D)    = M⁺ (wk⊢ P D)


-- --------------------------------------------------------------------------
--
-- Contraction


data _≳_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≳ ∅

  once : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
       → Γ ≳ Γ′
       → (Γ , A) ≳ (Γ′ , A)

  more : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
       → Γ ≳ Γ′
       → ((Γ , A) , A) ≳ (Γ′ , A)


cn∈ : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
    → Γ ≳ Γ′    → A ∈ Γ
    → A ∈ Γ′
cn∈ base     ()
cn∈ (once P) Z     = Z
cn∈ (once P) (S i) = S cn∈ P i
cn∈ (more P) Z     = Z
cn∈ (more P) (S i) = cn∈ (once P) i


cn⊢ : ∀{m m′ n} {Γ : Cx m} {Γ′ : Cx m′} {A : Hyp n}
     → Γ ≳ Γ′    → Γ ⊢ A
     → Γ′ ⊢ A
cn⊢ P (M𝑣 i)    = M𝑣 (cn∈ P i)
cn⊢ P (M𝜆 D)    = M𝜆 (cn⊢ (once P) D)
cn⊢ P (M∘ D D′) = M∘ (cn⊢ P D) (cn⊢ P D′)
cn⊢ P (M𝑝 D D′) = M𝑝 (cn⊢ P D) (cn⊢ P D′)
cn⊢ P (M𝜋₀ D)   = M𝜋₀ (cn⊢ P D)
cn⊢ P (M𝜋₁ D)   = M𝜋₁ (cn⊢ P D)
cn⊢ P (M⇑ D)    = M⇑ (cn⊢ P D)
cn⊢ P (M⇓ D)    = M⇓ (cn⊢ P D)
cn⊢ P (M⁻ D)    = M⁻ (cn⊢ P D)
cn⊢ P (M⁺ D)    = M⁺ (cn⊢ P D)


-- --------------------------------------------------------------------------
--
-- Exchange


data _≈_ : ∀{m} → Cx m → Cx m → Set where
  base : ∅ ≈ ∅

  just : ∀{m n} {Γ Γ′ : Cx m} {A : Hyp n}
       → Γ ≈ Γ′
       → (Γ , A) ≈ (Γ′ , A)

  same : ∀{m n k} {Γ Γ′ : Cx m} {A : Hyp n} {B : Hyp k}
       → Γ ≈ Γ′
       → ((Γ , A) , B) ≈ ((Γ′ , A) , B)

  diff : ∀{m n k} {Γ Γ′ : Cx m} {A : Hyp n} {B : Hyp k}
       → Γ ≈ Γ′
       → ((Γ , B) , A) ≈ ((Γ′ , A) , B)


ex∈ : ∀{m n} {Γ Γ′ : Cx m} {A : Hyp n}
    → Γ ≈ Γ′    → A ∈ Γ
    → A ∈ Γ′
ex∈ base     ()
ex∈ (just P) Z         = Z
ex∈ (just P) (S i)     = S ex∈ P i
ex∈ (same P) Z         = Z
ex∈ (same P) (S Z)     = S Z
ex∈ (same P) (S (S i)) = S (S ex∈ P i)
ex∈ (diff P) Z         = S Z
ex∈ (diff P) (S Z)     = Z
ex∈ (diff P) (S (S i)) = S (S ex∈ P i)


ex⊢ : ∀{m n} {Γ Γ′ : Cx m} {A : Hyp n}
     → Γ ≈ Γ′    → Γ ⊢ A
     → Γ′ ⊢ A
ex⊢ P (M𝑣 i)    = M𝑣 (ex∈ P i)
ex⊢ P (M𝜆 D)    = M𝜆 (ex⊢ (just P) D)
ex⊢ P (M∘ D D′) = M∘ (ex⊢ P D) (ex⊢ P D′)
ex⊢ P (M𝑝 D D′) = M𝑝 (ex⊢ P D) (ex⊢ P D′)
ex⊢ P (M𝜋₀ D)   = M𝜋₀ (ex⊢ P D)
ex⊢ P (M𝜋₁ D)   = M𝜋₁ (ex⊢ P D)
ex⊢ P (M⇑ D)    = M⇑ (ex⊢ P D)
ex⊢ P (M⇓ D)    = M⇓ (ex⊢ P D)
ex⊢ P (M⁻ D)    = M⁻ (ex⊢ P D)
ex⊢ P (M⁺ D)    = M⁺ (ex⊢ P D)


-- --------------------------------------------------------------------------
--
-- Theorem 1 (Internalisation principle), p. 29 [1]


prefixHyp : ∀{n} → Tm → Hyp n → Hyp (suc n)
prefixHyp t ⟨ ts ∷ A ⟩ = ⟨ t ‘ ts ∷ A ⟩

prefixCx : ∀{m} → Tms m → Cx m → Cx m
prefixCx []       ∅       = ∅
prefixCx (t ‘ ts) (Γ , h) = prefixCx ts Γ , prefixHyp t h


int∈ : ∀{m n} {xs : Vars m} {Γ : Cx m} {A : Hyp n}
     → A ∈ Γ
     → Σ Var (λ x → prefixHyp (𝑣 x) A ∈ prefixCx (map 𝑣_ xs) Γ)
int∈ {xs = []}     ()
int∈ {xs = x ‘ xs} Z     = ⟨ x , Z ⟩
int∈ {xs = x ‘ xs} (S i) = let ⟨ y , j ⟩ = int∈ {xs = xs} i in ⟨ y , S j ⟩


postulate
  fresh : Var  -- XXX: Fix this!


-- int⊢ : ∀{m n} {xs : Vars m} {Γ : Cx m} {A : Hyp n}
--       → Γ ⊢ A
--       → Σ (Vars m → Tm)
--            (λ t → prefixCx (map 𝑣_ xs) Γ ⊢ prefixHyp (t xs) A)

-- int⊢ {xs = xs} (M𝑣 {ts = ts} i)
--   = let ⟨ x , j ⟩ = int∈ {xs = xs} i
--     in
--       ⟨ (λ _ → 𝑣 x)
--       , M𝑣 {ts = 𝑣 x ‘ ts} j
--       ⟩

-- int⊢ {xs = xs} (M𝜆 {n = n} {xs = ys} {ts = ts} D)
--   = let xₘ₊₁      = fresh
--         ⟨ s , C ⟩ = int⊢ {xs = xₘ₊₁ ‘ xs} D
--     in
--       ⟨ (λ xs → 𝜆[ suc n ] xₘ₊₁ · s (xₘ₊₁ ‘ xs))
--       , M𝜆 {xs = xₘ₊₁ ‘ ys} {ts = s (xₘ₊₁ ‘ xs) ‘ ts} C
--       ⟩

-- int⊢ {xs = xs} (M∘ {n = n} {ts = ts} {ss = ss} D D′)
--   = let ⟨ s , C ⟩   = int⊢ {xs = xs} D
--         ⟨ s′ , C′ ⟩ = int⊢ {xs = xs} D′
--     in
--       ⟨ (λ xs → s xs ∘[ suc n ] s′ xs)
--       , M∘ {ts = s xs ‘ ts} {ss = s′ xs ‘ ss} C C′
--       ⟩

-- int⊢ {xs = xs} (M𝑝 {n = n} {ts = ts} {ss = ss} D D′)
--   = let ⟨ s , C ⟩   = int⊢ {xs = xs} D
--         ⟨ s′ , C′ ⟩ = int⊢ {xs = xs} D′
--     in
--       ⟨ (λ xs → 𝑝[ suc n ]⟨ s xs , s′ xs ⟩)
--       , M𝑝 {ts = s xs ‘ ts} {ss = s′ xs ‘ ss} C C′
--       ⟩

-- int⊢ {xs = xs} (M𝜋₀ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ (λ xs → 𝜋₀[ suc n ] s xs)
--       , M𝜋₀ {ts = s xs ‘ ts} C
--       ⟩

-- int⊢ {xs = xs} (M𝜋₁ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ (λ xs → 𝜋₁[ suc n ] s xs)
--       , M𝜋₁ {ts = s xs ‘ ts} C
--       ⟩

-- int⊢ {xs = xs} (M⇑ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ (λ xs → ⇑[ suc n ] s xs)
--       , M⇑ {ts = s xs ‘ ts} C
--       ⟩

-- int⊢ {xs = xs} (M⇓ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ (λ xs → ⇓[ suc n ] s xs)
--       , M⇓ {ts = s xs ‘ ts} C
--       ⟩

-- {-

--       → Σ (Vars m → Tm) (λ t → prefixCx (map 𝑣_ xs) Γ ⊢ prefixHyp (t xs) A)

--   M⁻  : ∀{A u n} {ts : Tms n}
--       → Γ ⊢ ts          ∷ u ∶ A
--       → Γ ⊢ append ts u ∷ A

--   M⁺  : ∀{A u n} {ts : Tms n}
--       → Γ ⊢ append ts u ∷ A
--       → Γ ⊢ ts          ∷ u ∶ A

-- -}


-- int⊢ {xs = xs} (M⁻ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ ((λ _ → {!!}))
--       , M⁻ {ts = {!!}} C
--       ⟩

-- int⊢ {xs = xs} (M⁺ {n = n} {ts = ts} D)
--   = let ⟨ s , C ⟩ = int⊢ {xs = xs} D
--     in
--       ⟨ ((λ xs → {!!}))
--       , M⁺ {ts = {!!}} C
--       ⟩

-- -- --------------------------------------------------------------------------
-- --
-- -- Work in progress

-- -- data _·≲_ : ∀{m} → Cx m → Cx m → Set where
-- --   base : ∅ ·≲ ∅
-- --   hold : ∀{m n} {Γ Γ′ : Cx m} {h : Hyp n}  → Γ ·≲ Γ′  → (Γ , h) ·≲ (Γ′ , h)
-- --   weak : ∀{m n t} {Γ Γ′ : Cx m} {h : Hyp n}  → Γ ·≲ Γ′  → (Γ , h) ·≲ (Γ′ , pwkHyp t h)

-- -- pwk∈ : ∀{m n t} {Γ Γ′ : Cx m} {h : Hyp n}  → Γ ·≲ Γ′  → h ∈ Γ  → pwkHyp t h ∈ Γ′
-- -- pwk∈ base     ()
-- -- pwk∈ (hold p) Z     = {!Z!}
-- -- pwk∈ (hold p) (S i) = {!!}
-- -- pwk∈ (weak p) i     = {!!}


-- -- in∈ : ∀{m n} {vs : Vars m} {Γ : Cx m} {h : Hyp n}
-- --     → h ∈ Γ  → Σ Var (λ x → pwkHyp (𝑣 x) h ∈ Γ)
-- -- in∈ {vs = ∅}      ()
-- -- in∈ {vs = x ‘ vs} Z     = {!x , Z!}
-- -- in∈ {vs = x ‘ vs} (S i) = {!!}

-- -- in⊢ : ∀{m n} {vs : Vars m} {Γ : Cx m} {h : Hyp n}
-- --     → Γ ⊢ h  → Σ (Vars m → Tm) (λ t → pwkHyps (map 𝑣_ vs) Γ ⊢ pwkHyp (t vs) h)
-- -- in⊢ d = {!!}

-- -- nec : ∀{n} {h : Hyp n}  → ∅ ⊢ h  → Σ Tm (λ t → ∅ ⊢ pwkHyp t h)
-- -- nec d = let s , c = in⊢ d in s ∅ , c


-- -- normHyp : ∀{n} → Tms n → Ty → Σ ℕ (λ n′ → Hyp n′)
-- -- normHyp {n} ts ⊥       = n , (ts , ⊥)
-- -- normHyp {n} ts (A ⊃ B) = n , (ts , (A ⊃ B))
-- -- normHyp {n} ts (A ∧ B) = n , (ts , (A ∧ B))
-- -- normHyp {n} ts (t ∶ A) = normHyp (app ts t) A
