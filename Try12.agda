{-# OPTIONS --allow-unsolved-metas #-}

{-

'(agda-input-user-translations
   (quote
    (("i" "⊃") ("e" "⊢") ("t" "⊩") ("N" "ℕ")
     ("Mv" "M𝑣") ("v" "𝑣") ("v0" "𝑣⁰") ("v1" "𝑣¹") ("v2" "𝑣²") ("v3" "𝑣³") ("vn" "𝑣ⁿ")
     ("Ml" "M𝜆") ("l" "𝜆") ("l0" "𝜆⁰") ("l1" "𝜆¹") ("l2" "𝜆²") ("l3" "𝜆³") ("ln" "𝜆ⁿ")
     ("Mo" "M∘") ("o" "∘") ("o0" "∘⁰") ("o1" "∘¹") ("o2" "∘²") ("o3" "∘³") ("on" "∘ⁿ")
     ("Mp" "M𝑝") ("p" "𝑝") ("p0" "𝑝⁰") ("p1" "𝑝¹") ("p2" "𝑝²") ("p3" "𝑝³") ("pn" "𝑝ⁿ")
     ("M1" "M𝜋₀") ("1" "𝜋₀") ("10" "𝜋₀⁰") ("11" "𝜋₀¹") ("12" "𝜋₀²") ("13" "𝜋₀³") ("1n" "𝜋₀ⁿ")
     ("M2" "M𝜋₁") ("2" "𝜋₁") ("20" "𝜋₁⁰") ("21" "𝜋₁¹") ("22" "𝜋₁²") ("23" "𝜋₁³") ("2n" "𝜋₁ⁿ")
     ("Mu" "M⇑") ("u" "⇑") ("u0" "⇑⁰") ("u1" "⇑¹") ("u2" "⇑²") ("u3" "⇑³") ("un" "⇑ⁿ")
     ("Md" "M⇓") ("d" "⇓") ("d0" "⇓⁰") ("d1" "⇓¹") ("d2" "⇓²") ("d3" "⇓³") ("dn" "⇓ⁿ")
     ("M-" "M⁻") ("M+" "M⁺"))))

-}

module Try12 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ) renaming (_,_ to ⟨_,_⟩)

infixl 5 _∘_ _∘²_
infixr 4 𝜆_,_ 𝜆²_,_
infixr 3 _∶_
infixr 3 _‘_
infixl 3 _,_
infixl 2 _∧_
infixr 1 _⊃_
infixr 1 _⊃⊂_
infixr 0 _⊢_∷_
infixr 0 ⊩_ ⊩_∷_ ⊩_∷_∷_



Var : Set
Var = ℕ


mutual
  data Ty : Set where
    ⊥   : Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _∶_ : Tm → Ty → Ty

  data Tm : Set where
    𝑣_        : Var → Tm
    𝜆[_]_,_   : ℕ → Var → Tm → Tm
    _∘[_]_    : Tm → ℕ → Tm → Tm
    𝑝[_]⟨_,_⟩ : ℕ → Tm → Tm → Tm
    𝜋₀[_]_    : ℕ → Tm → Tm
    𝜋₁[_]_    : ℕ → Tm → Tm
    !_        : Tm → Tm
    ⇑[_]_     : ℕ → Tm → Tm
    ⇓[_]_     : ℕ → Tm → Tm


⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


𝜆_,_ : Var → Tm → Tm
𝜆 x , t = 𝜆[ 1 ] x , t

𝜆²_,_ : Var → Tm → Tm
𝜆² x₂ , t₂ = 𝜆[ 2 ] x₂ , t₂

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘[ 1 ] s

_∘²_ : Tm → Tm → Tm
t₂ ∘² s₂ = t₂ ∘[ 2 ] s₂

𝑝⟨_,_⟩ : Tm → Tm → Tm
𝑝⟨ t , s ⟩ = 𝑝[ 1 ]⟨ t , s ⟩

𝑝²⟨_,_⟩ : Tm → Tm → Tm
𝑝²⟨ t₂ , s₂ ⟩ = 𝑝[ 2 ]⟨ t₂ , s₂ ⟩

𝜋₀_ : Tm → Tm
𝜋₀ t = 𝜋₀[ 1 ] t

𝜋₀²_ : Tm → Tm
𝜋₀² t₂ = 𝜋₀[ 2 ] t₂

𝜋₁_ : Tm → Tm
𝜋₁ t = 𝜋₁[ 1 ] t

𝜋₁²_ : Tm → Tm
𝜋₁² t₂ = 𝜋₁[ 2 ] t₂

⇑_ : Tm → Tm
⇑ t = ⇑[ 1 ] t

⇑²_ : Tm → Tm
⇑² t₂ = ⇑[ 2 ] t₂

⇓_ : Tm → Tm
⇓ t = ⇓[ 1 ] t

⇓²_ : Tm → Tm
⇓² t₂ = ⇓[ 2 ] t₂


data Vec (X : Set) : ℕ → Set where
  ∅   : Vec X zero
  _‘_ : ∀{n} → X → Vec X n → Vec X (suc n)


_“_ : ∀{n m} {X : Set} → Vec X n → Vec X m → Vec X (n + m)
∅        “ ys = ys
(x ‘ xs) “ ys = x ‘ xs “ ys


foldr : ∀{n} {X : Set} (Y : ℕ → Set) → (∀{k} → X → Y k → Y (suc k)) → Y zero → Vec X n → Y n
foldr Y f y₀ ∅        = y₀
foldr Y f y₀ (x ‘ xs) = f x (foldr Y f y₀ xs)

ixMap : ∀{n} {X Y : Set} → (ℕ → X → Y) → Vec X n → Vec Y n
ixMap {zero}  f ∅        = ∅
ixMap {suc n} f (x ‘ xs) = f (suc n) x ‘ ixMap f xs

ixZipWith : ∀{n} {X Y Z : Set} → (ℕ → X → Y → Z) → Vec X n → Vec Y n → Vec Z n
ixZipWith {zero}  f ∅        ∅        = ∅
ixZipWith {suc n} f (x ‘ xs) (y ‘ ys) = f (suc n) x y ‘ ixZipWith f xs ys

map : ∀{n} {X Y : Set} → (X → Y) → Vec X n → Vec Y n
map f = ixMap (λ _ x → f x)

zipWith : ∀{n} {X Y Z : Set} → (X → Y → Z) → Vec X n → Vec Y n → Vec Z n
zipWith f = ixZipWith (λ _ x y → f x y)


Vars : ℕ → Set
Vars = Vec Var

Tms : ℕ → Set
Tms = Vec Tm


𝑣ⁿ_ : ∀{n} → Vars n → Tms n
𝑣ⁿ_ = map 𝑣_

𝜆ⁿ_,_ : ∀{n} → Vars n → Tms n → Tms n
𝜆ⁿ_,_ = ixZipWith 𝜆[_]_,_

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


record Hyp : Set where
  constructor H[_]_∷_
  field
    n  : ℕ
    ts : Tms n
    A  : Ty

data Cx : ℕ → Set where
  ∅   : Cx zero
  _,_ : ∀{m} → Cx m → Hyp → Cx (suc m)

data _∈_  : ∀{m} → Hyp → Cx m → Set where
  Z  : ∀{m} {Γ : Cx m} {h : Hyp}  → h ∈ (Γ , h)
  S_ : ∀{m} {Γ : Cx m} {h h′ : Hyp}  → h ∈ Γ  → h ∈ (Γ , h′)


data _⊢_∷_ {m : ℕ} (Γ : Cx m) : ∀{n} → Tms n → Ty → Set where
  M𝑣_ : ∀{n A} {ts : Tms n}  → (H[ n ] ts ∷ A) ∈ Γ
                             → Γ ⊢ ts ∷ A

  M𝜆 : ∀{n A B} {xs : Vars n} {ts : Tms n}  → Γ , H[ n ] 𝑣ⁿ xs ∷ A ⊢ ts ∷ B
                                            → Γ ⊢ 𝜆ⁿ xs , ts ∷ A ⊃ B

  M∘ : ∀{n A B} {ts ss : Tms n}  → Γ ⊢ ts ∷ A ⊃ B  → Γ ⊢ ss ∷ A
                                 → Γ ⊢ ts ∘ⁿ ss ∷ B

  M𝑝 : ∀{n A B} {ts ss : Tms n}  → Γ ⊢ ts ∷ A  → Γ ⊢ ss ∷ B
                                 → Γ ⊢ 𝑝ⁿ⟨ ts , ss ⟩ ∷ A ∧ B

  M𝜋₀ : ∀{n A B} {ts : Tms n}  → Γ ⊢ ts ∷ A ∧ B
                               → Γ ⊢ 𝜋₀ⁿ ts ∷ A

  M𝜋₁ : ∀{n A B} {ts : Tms n}  → Γ ⊢ ts ∷ A ∧ B
                               → Γ ⊢ 𝜋₁ⁿ ts ∷ B

  M⇑ : ∀{n A u} {ts : Tms n}  → Γ ⊢ ts ∷ u ∶ A
                              → Γ ⊢ ⇑ⁿ ts ∷ ! u ∶ u ∶ A

  M⇓ : ∀{n A u} {ts : Tms n}  → Γ ⊢ ts ∷ u ∶ A
                              → Γ ⊢ ⇓ⁿ ts ∷ A

  M⁻ : ∀{n A u} {ts : Tms n}  → Γ ⊢ ts ∷ u ∶ A
                              → Γ ⊢ ts “ (u ‘ ∅) ∷ A

  M⁺ : ∀{n A u} {ts : Tms n}  → Γ ⊢ ts “ (u ‘ ∅) ∷ A
                              → Γ ⊢ ts ∷ u ∶ A


⊩_ : Ty → Set
⊩ A = ∀{m} {Γ : Cx m} → Γ ⊢ ∅ ∷ A

⊩_∷_ : Tm → Ty → Set
⊩ t ∷ A = ∀{m} {Γ : Cx m} → Γ ⊢ t ‘ ∅ ∷ A

⊩_∷_∷_ : Tm → Tm → Ty → Set
⊩ t₂ ∷ t ∷ A = ∀{m} {Γ : Cx m} → Γ ⊢ t₂ ‘ t ‘ ∅ ∷ A


eI⁰ : ∀{A}
    → ⊩ A ⊃ A
eI⁰ = M𝜆 (M𝑣 Z)

eI¹ : ∀{A x}
    → ⊩ 𝜆 x , 𝑣 x
      ∷ A ⊃ A
eI¹ = M𝜆 (M𝑣 Z)

eI² : ∀{A x u}
    → ⊩ 𝜆² u , 𝑣 u
      ∷ 𝜆 x , 𝑣 x
      ∷ A ⊃ A
eI² = M𝜆 (M𝑣 Z)


eK⁰ : ∀{A B}
    → ⊩ A ⊃ B ⊃ A
eK⁰ = M𝜆 (M𝜆 (M𝑣 S Z))

eK¹ : ∀{A B x y}
    → ⊩ 𝜆 x , 𝜆 y , 𝑣 x
      ∷ A ⊃ B ⊃ A
eK¹ = M𝜆 (M𝜆 (M𝑣 S Z))

eK² : ∀{A B x y u v}
    → ⊩ 𝜆² u , 𝜆² v , 𝑣 u
      ∷ 𝜆 x , 𝜆 y , 𝑣 x
      ∷ A ⊃ B ⊃ A
eK² = M𝜆 (M𝜆 (M𝑣 S Z))


eS⁰ : ∀{A B C}
    → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS⁰ = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 S S Z)
                         (M𝑣 Z))
                     (M∘ (M𝑣 S Z)
                         (M𝑣 Z)))))

eS¹ : ∀{A B C f g x}
    → ⊩ 𝜆 f , 𝜆 g , 𝜆 x , (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
      ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS¹ = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 S S Z)
                         (M𝑣 Z))
                     (M∘ (M𝑣 S Z)
                         (M𝑣 Z)))))

eS² : ∀{A B C f g x p q u}
    → ⊩ 𝜆² p , 𝜆² q , 𝜆² u , (𝑣 p ∘² 𝑣 u) ∘² (𝑣 q ∘² 𝑣 u)
      ∷ 𝜆 f , 𝜆 g , 𝜆 x , (𝑣 f ∘ 𝑣 x) ∘ (𝑣 g ∘ 𝑣 x)
      ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS² = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 S S Z)
                         (M𝑣 Z))
                     (M∘ (M𝑣 S Z)
                         (M𝑣 Z)))))


e11 : ∀{A x y}
    → ⊩ 𝜆 y , ⇓ 𝑣 y
      ∷ x ∶ A ⊃ A
e11 = M𝜆 (M⇓ (M𝑣 Z))

e12 : ∀{A x y}
    → ⊩ 𝜆 y , ⇑ 𝑣 y
      ∷ x ∶ A ⊃ ! x ∶ x ∶ A
e12 = M𝜆 (M⇑ (M𝑣 Z))

e13 : ∀{A B x y u v}
    → ⊩ 𝜆² u , 𝜆² v , 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
      ∷ 𝜆 x , 𝜆 y , 𝑝⟨ 𝑣 x , 𝑣 y ⟩
      ∷ A ⊃ B ⊃ A ∧ B
e13 = M𝜆 (M𝜆 (M𝑝 (M𝑣 S Z)
                 (M𝑣 Z)))

e14 : ∀{A B x y u v}
    → ⊩ 𝜆 u , 𝜆 v , ⇑ 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
      ∷ x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
e14 = M𝜆 (M𝜆 (M⇑ (M⁺ (M𝑝 (M⁻ (M𝑣 S Z))
                         (M⁻ (M𝑣 Z))))))


t0 : ∀{A B x y u v}
   → ⊩ 𝜆 u , 𝜆 v , 𝑝²⟨ 𝑣 u , 𝑣 v ⟩
     ∷ x ∶ A ⊃ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
t0 = M𝜆 (M𝜆 (M⁺ (M𝑝 (M⁻ (M𝑣 S Z))
                    (M⁻ (M𝑣 Z)))))

t1 : ∀{A B x y u}
   → ⊩ 𝜆 u , 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
     ∷ x ∶ A ∧ y ∶ B ⊃ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
t1 = M𝜆 (M⁺ (M𝑝 (M⁻ (M𝜋₀ (M𝑣 Z)))
                (M⁻ (M𝜋₁ (M𝑣 Z)))))

t2 : ∀{A B x y u}
   → ⊩ 𝜆 u , ⇑ 𝑝²⟨ 𝜋₀ 𝑣 u , 𝜋₁ 𝑣 u ⟩
     ∷ x ∶ A ∧ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B)
t2 = M𝜆 (M⇑ (M⁺ (M𝑝 (M⁻ (M𝜋₀ (M𝑣 Z)))
                    (M⁻ (M𝜋₁ (M𝑣 Z))))))


axK : ∀{A B f x p u}
    → ⊩ 𝜆 p , 𝜆 u , 𝑣 p ∘² 𝑣 u
      ∷ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
axK = M𝜆 (M𝜆 (M⁺ (M∘ (M⁻ (M𝑣 S Z))
                     (M⁻ (M𝑣 Z)))))

axT : ∀{A x u}
    → ⊩ 𝜆 u , ⇓ 𝑣 u
      ∷ x ∶ A ⊃ A
axT = e11

ax4 : ∀{A x u}
    → ⊩ 𝜆 u , ⇑ 𝑣 u
      ∷ x ∶ A ⊃ ! x ∶ x ∶ A
ax4 = e12


e2 : ∀{A x₃ x₂ x₁}
   → ⊩ 𝜆² x₃ , ⇓² ⇑² 𝑣 x₃
     ∷ 𝜆 x₂ , ⇓ ⇑ 𝑣 x₂
     ∷ x₁ ∶ A ⊃ x₁ ∶ A
e2 = M𝜆 (M⇓ (M⇑ (M𝑣 Z)))

e2′ : ∀{A x₃ x₂ x₁}
    → ⊩ 𝜆² x₃ , 𝑣 x₃
      ∷ 𝜆 x₂ , 𝑣 x₂
      ∷ x₁ ∶ A ⊃ x₁ ∶ A
e2′ = M𝜆 (M𝑣 Z)


_⊢_ : ∀{m} (Γ : Cx m) (h : Hyp) → Set
Γ ⊢ (H[ n ] ts ∷ A) = Γ ⊢ ts ∷ A


data _≲_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≲ ∅
  keep : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≲ Γ′  → (Γ , h) ≲ (Γ′ , h)
  drop : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≲ Γ′  → Γ ≲ (Γ′ , h)

∅≲Γ : ∀{m} {Γ : Cx m} → ∅ ≲ Γ
∅≲Γ {Γ = ∅}     = base
∅≲Γ {Γ = Γ , h} = drop ∅≲Γ

Γ≲Γ : ∀{m} {Γ : Cx m} → Γ ≲ Γ
Γ≲Γ {Γ = ∅}     = base
Γ≲Γ {Γ = Γ , h} = keep Γ≲Γ

wk∈ : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≲ Γ′  → h ∈ Γ  → h ∈ Γ′
wk∈ base     ()
wk∈ (keep p) Z     = Z
wk∈ (keep p) (S i) = S wk∈ p i
wk∈ (drop p) i     = S wk∈ p i

wk⊢ : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≲ Γ′  → Γ ⊢ h  → Γ′ ⊢ h
wk⊢ p (M𝑣 i)    = M𝑣 (wk∈ p i)
wk⊢ p (M𝜆 d)    = M𝜆 (wk⊢ (keep p) d)
wk⊢ p (M∘ d d′) = M∘ (wk⊢ p d) (wk⊢ p d′)
wk⊢ p (M𝑝 d d′) = M𝑝 (wk⊢ p d) (wk⊢ p d′)
wk⊢ p (M𝜋₀ d)   = M𝜋₀ (wk⊢ p d)
wk⊢ p (M𝜋₁ d)   = M𝜋₁ (wk⊢ p d)
wk⊢ p (M⇑ d)    = M⇑ (wk⊢ p d)
wk⊢ p (M⇓ d)    = M⇓ (wk⊢ p d)
wk⊢ p (M⁻ d)    = M⁻ (wk⊢ p d)
wk⊢ p (M⁺ d)    = M⁺ (wk⊢ p d)


data _≳_ : ∀{m m′} → Cx m → Cx m′ → Set where
  base : ∅ ≳ ∅
  once : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≳ Γ′  → (Γ , h) ≳ (Γ′ , h)
  more : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≳ Γ′  → (Γ , h , h) ≳ (Γ′ , h)

cn∈ : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≳ Γ′  → h ∈ Γ  → h ∈ Γ′
cn∈ base     ()
cn∈ (once p) Z     = Z
cn∈ (once p) (S i) = S cn∈ p i
cn∈ (more p) Z     = Z
cn∈ (more p) (S i) = cn∈ (once p) i

cn⊢ : ∀{m m′ h} {Γ : Cx m} {Γ′ : Cx m′}  → Γ ≳ Γ′  → Γ ⊢ h  → Γ′ ⊢ h
cn⊢ p (M𝑣 i)    = M𝑣 (cn∈ p i)
cn⊢ p (M𝜆 d)    = M𝜆 (cn⊢ (once p) d)
cn⊢ p (M∘ d d′) = M∘ (cn⊢ p d) (cn⊢ p d′)
cn⊢ p (M𝑝 d d′) = M𝑝 (cn⊢ p d) (cn⊢ p d′)
cn⊢ p (M𝜋₀ d)   = M𝜋₀ (cn⊢ p d)
cn⊢ p (M𝜋₁ d)   = M𝜋₁ (cn⊢ p d)
cn⊢ p (M⇑ d)    = M⇑ (cn⊢ p d)
cn⊢ p (M⇓ d)    = M⇓ (cn⊢ p d)
cn⊢ p (M⁻ d)    = M⁻ (cn⊢ p d)
cn⊢ p (M⁺ d)    = M⁺ (cn⊢ p d)


data _≈_ : ∀{m} → Cx m → Cx m → Set where
  base : ∅ ≈ ∅
  just : ∀{m h} {Γ Γ′ : Cx m}  → Γ ≈ Γ′  → (Γ , h) ≈ (Γ′ , h)
  same : ∀{m h h′}  {Γ Γ′ : Cx m}  → Γ ≈ Γ′  → (Γ , h , h′) ≈ (Γ′ , h , h′)
  diff : ∀{m h h′}  {Γ Γ′ : Cx m}  → Γ ≈ Γ′  → (Γ , h′ , h) ≈ (Γ′ , h , h′)

ex∈ : ∀{m h} {Γ Γ′ : Cx m}  → Γ ≈ Γ′  → h ∈ Γ  → h ∈ Γ′
ex∈ base     ()
ex∈ (just p) Z         = Z
ex∈ (just p) (S i)     = S ex∈ p i
ex∈ (same p) Z         = Z
ex∈ (same p) (S Z)     = S Z
ex∈ (same p) (S (S i)) = S (S ex∈ p i)
ex∈ (diff p) Z         = S Z
ex∈ (diff p) (S Z)     = Z
ex∈ (diff p) (S (S i)) = S (S ex∈ p i)

ex⊢ : ∀{m h} {Γ Γ′ : Cx m}  → Γ ≈ Γ′  → Γ ⊢ h  → Γ′ ⊢ h
ex⊢ p (M𝑣 i)    = M𝑣 (ex∈ p i)
ex⊢ p (M𝜆 d)    = M𝜆 (ex⊢ (just p) d)
ex⊢ p (M∘ d d′) = M∘ (ex⊢ p d) (ex⊢ p d′)
ex⊢ p (M𝑝 d d′) = M𝑝 (ex⊢ p d) (ex⊢ p d′)
ex⊢ p (M𝜋₀ d)   = M𝜋₀ (ex⊢ p d)
ex⊢ p (M𝜋₁ d)   = M𝜋₁ (ex⊢ p d)
ex⊢ p (M⇑ d)    = M⇑ (ex⊢ p d)
ex⊢ p (M⇓ d)    = M⇓ (ex⊢ p d)
ex⊢ p (M⁻ d)    = M⁻ (ex⊢ p d)
ex⊢ p (M⁺ d)    = M⁺ (ex⊢ p d)


postulate fresh : Var  -- XXX: Fix this!


toVec : ∀{m} → Cx m → Vec Hyp m
toVec ∅       = ∅
toVec (Γ , h) = h ‘ toVec Γ

fromVec : ∀{m} → Vec Hyp m → Cx m
fromVec ∅        = ∅
fromVec (h ‘ hs) = fromVec hs , h

prefixHyp : Tm → Hyp → Hyp
prefixHyp t (H[ n ] ts ∷ A) = H[ suc n ] (t ‘ ts) ∷ A

prefixHyps : ∀{m} → Tms m → Cx m → Cx m
prefixHyps ts Γ = fromVec (zipWith prefixHyp ts (toVec Γ))


in∈ : ∀{m h} {vs : Vars m} {Γ : Cx m}
    → h ∈ Γ  → Σ Var (λ x → prefixHyp (𝑣 x) h ∈ Γ)
in∈ {vs = ∅}      ()
in∈ {vs = x ‘ vs} Z     = {!⟨ x , Z ⟩!}
in∈ {vs = x ‘ vs} (S i) = {!!}

in⊢ : ∀{m h} {vs : Vars m} {Γ : Cx m}
    → Γ ⊢ h  → Σ (Vars m → Tm) (λ t → prefixHyps (map 𝑣_ vs) Γ ⊢ prefixHyp (t vs) h)
in⊢ d = {!!}

nec : ∀{h}  → ∅ ⊢ h  → Σ Tm (λ t → ∅ ⊢ prefixHyp t h)
nec d = let ⟨ s , c ⟩ = in⊢ d in ⟨ s ∅ , c ⟩
