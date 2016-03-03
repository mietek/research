{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

Checked with Agda 2.4.2.5.

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote
    (("N" "ℕ") ("not" "¬") ("imp" "⊃") ("iff" "⊃⊂") ("ent" "⊢") ("thm" "⊩") 
     ("s" "𝒔") ("t" "𝒕") ("x" "𝒙") ("y" "𝒚") ("A" "𝑨")
     ("v" "𝑣") ("v1" "𝑣") ("v2" "𝑣²") ("vn" "𝑣ⁿ")
     ("l" "𝜆") ("l1" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o" "∘") ("o1" "∘") ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝑝") ("p1" "𝑝") ("p2" "𝑝²") ("pn" "𝑝ⁿ")
     ("pi0" "𝜋₀") ("pi01" "𝜋₀") ("pi02" "𝜋₀²") ("pi0n" "𝜋₀ⁿ")
     ("pi1" "𝜋₁") ("pi11" "𝜋₁") ("pi12" "𝜋₁²") ("pi1n" "𝜋₁ⁿ")
     ("u" "⇑") ("u1" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d1" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))

[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
     2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
     Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}

module AltArtemov where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_)

infixl 9 _∘_ _∘²_ _∘^[_]_
infixr 8 𝑣_ !_ ⇓_ ⇑_ ⇓²_ ⇑²_ ⇓^[_]_ ⇑^[_]_ 
infixr 7 𝜆_．_ 𝜆²_．_ 𝜆^[_]_．_
infixr 6 _∶_
infixr 5 ¬_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_
infixr 0 _⊢_ ⊩_


------------------------------------------------------------------------------

-- System λ∞


mutual

  -- Variables

  Var : Set
  Var = ℕ


  -- Term constructors

  data Tm : Set where
    𝑣_         : (x : Var)                  → Tm    -- Variable
    𝜆^[_]_．_   : (n : ℕ) (x : Var) (t : Tm) → Tm    -- Abstraction
    _∘^[_]_    : (t : Tm) (n : ℕ) (s : Tm)  → Tm    -- Application
    𝑝^[_]⟨_,_⟩ : (n : ℕ) (t s : Tm)         → Tm    -- Pairing
    𝜋₀^[_]_    : (n : ℕ) (t : Tm)           → Tm    -- Left projection
    𝜋₁^[_]_    : (n : ℕ) (t : Tm)           → Tm    -- Right projection
    !_         : (t : Tm)                   → Tm    -- Proof checking
    ⇑^[_]_     : (n : ℕ) (t : Tm)           → Tm    -- Reification
    ⇓^[_]_     : (n : ℕ) (t : Tm)           → Tm    -- Reflection


  -- Type constructors

  data Ty : Set where
    ⊥   :                     Ty    -- Falsehood
    _⊃_ : (A B : Ty)        → Ty    -- Implication
    _∧_ : (A B : Ty)        → Ty    -- Conjunction
    _∶_ : (x : Tm) (A : Ty) → Ty    -- Provability


-- Additional types

⊤ : Ty                    -- Truth
⊤ = ⊥ ⊃ ⊥

¬_ : (A : Ty) → Ty        -- Negation
¬ A = A ⊃ ⊥

_⊃⊂_ : (A B : Ty) → Ty    -- Equivalence
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


------------------------------------------------------------------------------

-- Non-empty vectors

data Vec (X : Set) : ℕ → Set where
  _⋯ : (x₁ : X)                      → Vec X zero
  _∷_ : {n : ℕ} (xₙ : X) (𝒙 : Vec X n) → Vec X (suc n)

foldl : {n : ℕ} {X Y : Set} (f : Y → X → Y) (𝒙 : Vec X n) (y : Y) → Y
foldl f (x₁ ⋯)   y = f y x₁
foldl f (xₙ ∷ 𝒙) y = f (foldl f 𝒙 y) xₙ

foldr : {n : ℕ} {X Y : Set} (f : X → Y → Y) (𝒙 : Vec X n) (y : Y) → Y
foldr f (x₁ ⋯)   y = f x₁ y
foldr f (xₙ ∷ 𝒙) y = f xₙ (foldr f 𝒙 y)

map# : {n : ℕ} {X Y : Set} (f : ℕ → X → Y) (𝒙 : Vec X n) → Vec Y n
map# {zero}  f (x₁ ⋯)   = f zero    x₁ ⋯
map# {suc n} f (xₙ ∷ 𝒙) = f (suc n) xₙ ∷ map# f 𝒙

map : {n : ℕ} {X Y : Set} (f : X → Y) (𝒙 : Vec X n) → Vec Y n
map f 𝒙 = map# (λ _ x → f x) 𝒙

map2# : {n : ℕ} {X Y Z : Set} (f : ℕ → X → Y → Z) (𝒙 : Vec X n) (𝒚 : Vec Y n) → Vec Z n
map2# {zero}  f (x₁ ⋯)   (y₁ ⋯)   = f zero    x₁ y₁ ⋯
map2# {suc n} f (xₙ ∷ 𝒙) (yₙ ∷ 𝒚) = f (suc n) xₙ yₙ ∷ map2# f 𝒙 𝒚

map2 : {n : ℕ} {X Y Z : Set} (f : X → Y → Z) (𝒙 : Vec X n) (𝒚 : Vec Y n) → Vec Z n
map2 f 𝒙 𝒚 = map2# (λ _ x y → f x y) 𝒙 𝒚


-- XXX

VVar : ℕ → Set
VVar = Vec Var

VTm : ℕ → Set
VTm = Vec Tm

VTy : ℕ → Set
VTy n = Vec Ty n

V_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
V 𝒕 ∶ A = foldr _∶_ 𝒕 A


-- Vector notation for nested term constructors

𝑣ⁿ_∶_ : {n : ℕ} (𝒙 : VVar n) (A : Ty) → Ty
𝑣ⁿ 𝒙 ∶ A = V (map 𝑣_ 𝒙) ∶ A

𝜆ⁿ_．_∶_ : {n : ℕ} (𝒙 : VVar n) (𝒕 : VTm n) (A : Ty) → Ty
𝜆ⁿ 𝒙 ． 𝒕 ∶ A = V (map2# 𝜆^[_]_．_ 𝒙 𝒕) ∶ A

_∘ⁿ_∶_ : {n : ℕ} (𝒕 𝒔 : VTm n) (A : Ty) → Ty
𝒕 ∘ⁿ 𝒔 ∶ A = V (map2# (λ n t s → t ∘^[ n ] s) 𝒕 𝒔) ∶ A

𝑝ⁿ⟨_,_⟩∶_ : {n : ℕ} (𝒕 𝒔 : VTm n) (A : Ty) → Ty
𝑝ⁿ⟨ 𝒕 , 𝒔 ⟩∶ A = V (map2# 𝑝^[_]⟨_,_⟩ 𝒕 𝒔) ∶ A

𝜋₀ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
𝜋₀ⁿ 𝒕 ∶ A = V (map# 𝜋₀^[_]_ 𝒕) ∶ A

𝜋₁ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
𝜋₁ⁿ 𝒕 ∶ A = V (map# 𝜋₁^[_]_ 𝒕) ∶ A

⇑ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
⇑ⁿ 𝒕 ∶ A = V (map# ⇑^[_]_ 𝒕) ∶ A

⇓ⁿ_∶_ : {n : ℕ} (𝒕 : VTm n) (A : Ty) → Ty
⇓ⁿ 𝒕 ∶ A = V (map# ⇓^[_]_ 𝒕) ∶ A


------------------------------------------------------------------------------

-- Contexts

data Cx : Set where
  ∅   :                     Cx
  _,_ : (Γ : Cx) (A : Ty) → Cx


-- Context membership evidence

data _∈_ (A : Ty) : Cx → Set where
  Z : {Γ : Cx}                  → A ∈ Γ , A
  S : {Γ : Cx} {B : Ty} → A ∈ Γ → A ∈ Γ , B


-- Typing rules

data _⊢_ (Γ : Cx) : Ty → Set where
  R𝑣ⁿ  : {n : ℕ} {𝒙 : VVar n} {A : Ty}
       → 𝑣ⁿ 𝒙 ∶ A ∈ Γ
       → Γ ⊢ 𝑣ⁿ 𝒙 ∶ A

  R𝜆ⁿ  : {n : ℕ} {𝒙 : VVar n} {𝒕 : VTm n} {A B : Ty}
       → Γ , 𝑣ⁿ 𝒙 ∶ A ⊢ V 𝒕 ∶ B
       → Γ ⊢ 𝜆ⁿ 𝒙 ． 𝒕 ∶ (A ⊃ B)

  R∘ⁿ  : {n : ℕ} {𝒕 𝒔 : VTm n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ⊃ B)    → Γ ⊢ V 𝒔 ∶ A
       → Γ ⊢ 𝒕 ∘ⁿ 𝒔 ∶ B

  R𝑝ⁿ  : {n : ℕ} {𝒕 𝒔 : VTm n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ A    → Γ ⊢ V 𝒔 ∶ B
       → Γ ⊢ 𝑝ⁿ⟨ 𝒕 , 𝒔 ⟩∶ (A ∧ B)

  R𝜋₀ⁿ : {n : ℕ} {𝒕 : VTm n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₀ⁿ 𝒕 ∶ A

  R𝜋₁ⁿ : {n : ℕ} {𝒕 : VTm n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ∧ B)
       → Γ ⊢ 𝜋₁ⁿ 𝒕 ∶ B

  R⇑ⁿ  : {n : ℕ} {𝒕 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ V 𝒕 ∶ (u ∶ A)
       → Γ ⊢ ⇑ⁿ 𝒕 ∶ (! u ∶ u ∶ A)

  R⇓ⁿ  : {n : ℕ} {𝒕 : VTm n} {u : Tm} {A : Ty}
       → Γ ⊢ V 𝒕 ∶ (u ∶ A)
       → Γ ⊢ ⇓ⁿ 𝒕 ∶ A


-- Theorems

⊩_  : (A : Ty) → Set
⊩ A = {Γ : Cx} → Γ ⊢ A


------------------------------------------------------------------------------

-- Simplified notation for level 1 terms

𝜆_．_ : (x : Var) (t : Tm) → Tm
𝜆 x ． t = 𝜆^[ 0 ] x ． t

_∘_ : (t s : Tm) → Tm
t ∘ s = t ∘^[ 0 ] s

𝑝⟨_,_⟩ : (t s : Tm) → Tm
𝑝⟨ t , s ⟩ = 𝑝^[ 0 ]⟨ t , s ⟩

𝜋₀_ : (t : Tm) → Tm
𝜋₀ t = 𝜋₀^[ 0 ] t

𝜋₁_ : (t : Tm) → Tm
𝜋₁ t = 𝜋₁^[ 0 ] t

⇑_ : (t : Tm) → Tm
⇑ t = ⇑^[ 0 ] t

⇓_ : (t : Tm) → Tm
⇓ t = ⇓^[ 0 ] t


-- Simplified notation for level 2 terms

𝜆²_．_ : (x : Var) (t : Tm) → Tm
𝜆² x ． t = 𝜆^[ 1 ] x ． t

_∘²_ : (t s : Tm) → Tm
t ∘² s = t ∘^[ 1 ] s

𝑝²⟨_,_⟩ : (t s : Tm) → Tm
𝑝²⟨ t , s ⟩ = 𝑝^[ 1 ]⟨ t , s ⟩

𝜋₀²_ : (t : Tm) → Tm
𝜋₀² t = 𝜋₀^[ 1 ] t

𝜋₁²_ : (t : Tm) → Tm
𝜋₁² t = 𝜋₁^[ 1 ] t

⇑²_ : (t : Tm) → Tm
⇑² t = ⇑^[ 1 ] t

⇓²_ : (t : Tm) → Tm
⇓² t = ⇓^[ 1 ] t


-- Simplified notation for level 1 typing rules

R𝑣 : {x : Var} {A : Ty} {Γ : Cx}
   → 𝑣 x ∶ A ∈ Γ
   → Γ ⊢ 𝑣 x ∶ A
R𝑣 {x} = R𝑣ⁿ {𝒙 = x ⋯}

R𝜆 : {x : Var} {t : Tm} {A B : Ty} {Γ : Cx}
   → Γ , (𝑣 x ∶ A) ⊢ t ∶ B
   → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)
R𝜆 {x} {t} = R𝜆ⁿ {𝒙 = x ⋯} {𝒕 = t ⋯}

R∘ : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
   → Γ ⊢ t ∘ s ∶ B
R∘ {t} {s} = R∘ⁿ {𝒕 = t ⋯} {𝒔 = s ⋯}

R𝑝 : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
   → Γ ⊢ 𝑝⟨ t , s ⟩ ∶ (A ∧ B)
R𝑝 {t} {s} = R𝑝ⁿ {𝒕 = t ⋯} {𝒔 = s ⋯}

R𝜋₀ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₀ t ∶ A
R𝜋₀ {t} = R𝜋₀ⁿ {𝒕 = t ⋯}

R𝜋₁ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝜋₁ t ∶ B
R𝜋₁ {t} = R𝜋₁ⁿ {𝒕 = t ⋯}

R⇑ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
R⇑ {t} = R⇑ⁿ {𝒕 = t ⋯}

R⇓ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇓ t ∶ A
R⇓ {t} = R⇓ⁿ {𝒕 = t ⋯}


-- Simplified notation for level 2 typing rules

R𝑣² : {x₂ x₁ : Var} {A : Ty} {Γ : Cx}
    → 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ∈ Γ
    → Γ ⊢ 𝑣 x₂ ∶ 𝑣 x₁ ∶ A
R𝑣² {x₂} {x₁} = R𝑣ⁿ {𝒙 = x₂ ∷ x₁ ⋯}

R𝜆² : {x₂ x₁ : Var} {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ , (𝑣 x₂ ∶ 𝑣 x₁ ∶ A) ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)
R𝜆² {x₂} {x₁} {t₂} {t₁} = R𝜆ⁿ {𝒙 = x₂ ∷ x₁ ⋯} {𝒕 = t₂ ∷ t₁ ⋯}

R∘² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
R∘² {t₂} {t₁} {s₂} {s₁} = R∘ⁿ {𝒕 = t₂ ∷ t₁ ⋯} {𝒔 = s₂ ∷ s₁ ⋯}

R𝑝² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ A    → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝑝²⟨ t₂ , s₂ ⟩ ∶ 𝑝⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
R𝑝² {t₂} {t₁} {s₂} {s₁} = R𝑝ⁿ {𝒕 = t₂ ∷ t₁ ⋯} {𝒔 = s₂ ∷ s₁ ⋯}

R𝜋₀² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₀² t₂ ∶ 𝜋₀ t₁ ∶ A
R𝜋₀² {t₂} {t₁} = R𝜋₀ⁿ {𝒕 = t₂ ∷ t₁ ⋯}

R𝜋₁² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝜋₁² t₂ ∶ 𝜋₁ t₁ ∶ B
R𝜋₁² {t₂} {t₁} = R𝜋₁ⁿ {𝒕 = t₂ ∷ t₁ ⋯}

R⇑² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
R⇑² {t₂} {t₁} = R⇑ⁿ {𝒕 = t₂ ∷ t₁ ⋯}

R⇓² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
R⇓² {t₂} {t₁} = R⇓ⁿ {𝒕 = t₂ ∷ t₁ ⋯}


------------------------------------------------------------------------------

-- IKS combinators

EI : {x : Var} {A : Ty}
   → ⊩ 𝜆 x ． 𝑣 x ∶ (A ⊃ A)
EI = R𝜆 (R𝑣 Z)


EK : {x y : Var} {A B : Ty}
   → ⊩ 𝜆 x ． 𝜆 y ． 𝑣 x ∶ (A ⊃ B ⊃ A)
EK = R𝜆 (R𝜆 (R𝑣 (S Z)))


ES : {f g x : Var} {A B C : Ty}
   → ⊩ 𝜆 f ． 𝜆 g ． 𝜆 x ． ((𝑣 f) ∘ (𝑣 x)) ∘ ((𝑣 g) ∘ (𝑣 x)) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
ES = R𝜆 (R𝜆 (R𝜆 (R∘ (R∘ (R𝑣 (S (S Z)))
                        (R𝑣 Z))
                    (R∘ (R𝑣 (S Z))
                        (R𝑣 Z)))))


-- Example 1 (p. 28[1])

E1₁ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇓ 𝑣 y ∶ (𝑣 x ∶ A ⊃ A)
E1₁ = R𝜆 (R⇓ (R𝑣 Z))

E1₂ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇑ 𝑣 y ∶ (𝑣 x ∶ A ⊃ ! 𝑣 x ∶ 𝑣 x ∶ A)
E1₂ = R𝜆 (R⇑ (R𝑣 Z))

E1₃ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝑝²⟨ 𝑣 u , 𝑣 v ⟩ ∶ 𝜆 x ． 𝜆 y ． 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
E1₃ = R𝜆² (R𝜆² (R𝑝² (R𝑣² (S Z))
                    (R𝑣² Z)))

E1₄ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩ ∶ (𝑣 x ∶ A ⊃ 𝑣 y ∶ B ⊃ ! 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∶ 𝑝⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ∧ B))
E1₄ = R𝜆 (R𝜆 (R⇑ (R𝑝² (R𝑣 (S Z))
                      (R𝑣 Z))))


-- Example 2 (pp. 31–32[1])

E2  : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝑣 x₃ ∶ 𝜆 x₂ ． ⇓ ⇑ 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
E2  = R𝜆² (R⇓² (R⇑² (R𝑣² Z)))

E2' : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． 𝑣 x₃ ∶ 𝜆 x₂ ． 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
E2' = R𝜆² (R𝑣² Z)


------------------------------------------------------------------------------

-- Work in progress

{-
_V,_∶_ : {n : ℕ} (Γ : Cx) (𝒙 : VVar n) (𝑨 : VTy n) → Cx
Γ V, (x₁ ⋯)   ∶ (A₁ ⋯)   = Γ , (𝑣 x₁ ∶ A₁)
Γ V, (xₙ ∷ 𝒙) ∶ (Aₙ ∷ 𝑨) = (Γ V, 𝒙 ∶ 𝑨) , (𝑣 xₙ ∶ Aₙ)


-- "Note that the set of axioms is thus also defined inductively according to λ∞:
-- as soon as we are able to establish that F is a type we are entitled to use
-- variables of type F as new axioms."

postulate -- XXX: How to prove this?
  lem1 : {n m : ℕ} {x : Var} {𝒙 : VVar n} {𝒚 : VVar m} {A B : Ty} {Γ : Cx}
    → 𝑣ⁿ 𝒚 ∶ B ∈ Γ ,      𝑣ⁿ 𝒙 ∶ A
    → 𝑣ⁿ 𝒚 ∶ B ∈ Γ , (𝑣ⁿ x ∷ 𝒙 ∶ A)

  lem2 : {n m : ℕ} {x : Var} {𝒙 : VVar n} {𝒚 : VVar m} {𝒕 : VTm m} {A B C : Ty} {Γ : Cx}
    → (Γ ,      𝑣ⁿ 𝒙 ∶ A)  , 𝑣ⁿ 𝒚 ∶ B ⊢ V 𝒕 ∶ C
    → (Γ , (𝑣ⁿ x ∷ 𝒙 ∶ A)) , 𝑣ⁿ 𝒚 ∶ B ⊢ V 𝒕 ∶ C


weak : {n : ℕ} {x : Var} {𝒙 : VVar n} {A B : Ty} {Γ : Cx}
  → Γ ,        𝑣ⁿ 𝒙 ∶ A  ⊢ B
  → Γ , (𝑣 x ∶ 𝑣ⁿ 𝒙 ∶ A) ⊢ B
weak {n} {x} {𝒙} {A} (R𝑣ⁿ {m} {𝒚} D) = R𝑣ⁿ {𝒙 = 𝒚} (lem1 {𝒙 = 𝒙} {𝒚 = 𝒚} D)
weak {n} {x} {𝒙} (R𝜆ⁿ {m} {𝒚} {𝒕} D) = R𝜆ⁿ {𝒙 = 𝒚} {𝒕 = 𝒕} (lem2 {𝒙 = 𝒙} {𝒚 = 𝒚} {𝒕 = 𝒕} D)
weak {n} (R∘ⁿ {m} D₀ D₁)             = R∘ⁿ  {n = m} (weak {n} D₀) (weak {n} D₁)
weak {n} (R𝑝ⁿ {m} D₀ D₁)             = R𝑝ⁿ  {n = m} (weak {n} D₀) (weak {n} D₁)
weak {n} (R𝜋₀ⁿ {m} D)                = R𝜋₀ⁿ {n = m} (weak {n} D)
weak {n} (R𝜋₁ⁿ {m} D)                = R𝜋₁ⁿ {n = m} (weak {n} D)
weak {n} (R⇑ⁿ {m} D)                 = R⇑ⁿ  {n = m} (weak {n} D)
weak {n} (R⇓ⁿ {m} D)                 = R⇓ⁿ  {n = m} (weak {n} D)


-- "Let λ∞ derive
--   A₁, A₂, …, Aₘ ⊢ B.
-- Then one can build a well-defined term t(x₁, x₂, …, xₘ) with fresh variables 𝒙 such that λ∞ also derives
--   x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ ⊢ t(x₁, x₂, …, xₘ) ∶ B."

T1 : {m : ℕ} (𝒙 : VVar m) {𝑨 : VTy m} {B : Ty} {Γ : Cx}
  → Γ V, 𝒙 ∶ 𝑨 ⊢ B
  → Σ (VVar m → Tm) (λ t → (Γ V, 𝒙 ∶ 𝑨) ⊢ t 𝒙 ∶ B)

T1 𝒙 (R𝑣ⁿ {n} {𝒚} D) =
  T1 𝒙 (R𝑣ⁿ {𝒙 = 𝒚} D)

T1 {m} 𝒙 {𝑨} (R𝜆ⁿ {n} {𝒚} {𝒕} {A} D) =
  let xₘ₊₁  = suc m -- XXX: How to guarantee this to be a fresh variable?
      Aₘ₊₁  = 𝑣ⁿ 𝒚 ∶ A
      s , E = T1 (xₘ₊₁ ∷ 𝒙) {Aₘ₊₁ ∷ 𝑨} (weak {𝒙 = 𝒚} D)
  in (λ 𝒙 → 𝜆^[ suc n ] xₘ₊₁ ． s (xₘ₊₁ ∷ 𝒙))
    , R𝜆ⁿ {𝒙 = xₘ₊₁ ∷ 𝒚} {𝒕 = s (xₘ₊₁ ∷ 𝒙) ∷ 𝒕} E
     
T1 𝒙 (R∘ⁿ {n} {𝒕} {𝒔} Dₜ Dₛ) =
  let sₜ , Eₜ = T1 𝒙 Dₜ
      sₛ , Eₛ = T1 𝒙 Dₛ
  in  (λ 𝒙 → sₜ 𝒙 ∘^[ suc n ] sₛ 𝒙)
    , R∘ⁿ {𝒕 = sₜ 𝒙 ∷ 𝒕} {𝒔 = sₛ 𝒙 ∷ 𝒔} Eₜ Eₛ
     
T1 𝒙 (R𝑝ⁿ {n} {𝒕} {𝒔} Dₜ Dₛ) =
  let sₜ , Eₜ = T1 𝒙 Dₜ
      sₛ , Eₛ = T1 𝒙 Dₛ
  in  (λ 𝒙 → 𝑝^[ suc n ]⟨ sₜ 𝒙 , sₛ 𝒙 ⟩)
    , R𝑝ⁿ {𝒕 = sₜ 𝒙 ∷ 𝒕} {𝒔 = sₛ 𝒙 ∷ 𝒔} Eₜ Eₛ
     
T1 𝒙 (R𝜋₀ⁿ {n} {𝒕} D) =
  let s , E = T1 𝒙 D
  in  (λ 𝒙 → 𝜋₀^[ suc n ] s 𝒙)
    , R𝜋₀ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E
     
T1 𝒙 (R𝜋₁ⁿ {n} {𝒕} D) =
  let s , E = T1 𝒙 D
  in  (λ 𝒙 → 𝜋₁^[ suc n ] s 𝒙)
    , R𝜋₁ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E
     
T1 𝒙 (R⇑ⁿ {n} {𝒕} D) =
  let s , E = T1 𝒙 D
  in  (λ 𝒙 → ⇑^[ suc n ] s 𝒙)
    , R⇑ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E
     
T1 𝒙 (R⇓ⁿ {n} {𝒕} D) =
  let s , E = T1 𝒙 D
  in  (λ 𝒙 → ⇓^[ suc n ] s 𝒙)
    , R⇓ⁿ {𝒕 = s 𝒙 ∷ 𝒕} E
-}
