module A201605.AbelChapmanExtended.Syntax where




data Ty : Set where
  ⊥   :               Ty
  _⇒_ : (a b : Ty) → Ty
  _∧_  : (a b : Ty) → Ty
  ⊤   :               Ty

infixr 5 _⇒_


data Cx : Set where
  ∅   :                      Cx
  _,_ : (Γ : Cx) (a : Ty) → Cx

data Var : Cx → Ty → Set where
  top : ∀ {Γ a}                 → Var (Γ , a) a
  pop : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a


data Tm (Γ : Cx) : Ty → Set where
  loop : ∀ {c}   (t : Tm Γ ⊥)                    → Tm Γ c
  var  : ∀ {a}   (x : Var Γ a)                    → Tm Γ a
  lam  : ∀ {a b} (t : Tm (Γ , a) b)               → Tm Γ (a ⇒ b)
  app  : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b
  pair : ∀ {a b} (t : Tm Γ a)        (u : Tm Γ b) → Tm Γ (a ∧ b)
  fst  : ∀ {a b} (t : Tm Γ (a ∧ b))               → Tm Γ a
  snd  : ∀ {a b} (t : Tm Γ (a ∧ b))               → Tm Γ b
  unit :                                              Tm Γ ⊤


data Ne (Ξ : Cx → Ty → Set) (Γ : Cx) : Ty → Set where
  loop : ∀ {c}   → Ne Ξ Γ ⊥                → Ne Ξ Γ c
  var  : ∀ {a}   → Var Γ a                  → Ne Ξ Γ a
  app  : ∀ {a b} → Ne Ξ Γ (a ⇒ b) → Ξ Γ a → Ne Ξ Γ b
  fst  : ∀ {a b} → Ne Ξ Γ (a ∧ b)           → Ne Ξ Γ a
  snd  : ∀ {a b} → Ne Ξ Γ (a ∧ b)           → Ne Ξ Γ b

data Nf (Δ : Cx) : Ty → Set where
  ne   :          (n : Ne Nf Δ ⊥)          → Nf Δ ⊥
  lam  : ∀ {a b} (n : Nf (Δ , a) b)        → Nf Δ (a ⇒ b)
  pair : ∀ {a b} (n : Nf Δ a) (m : Nf Δ b) → Nf Δ (a ∧ b)
  unit :                                       Nf Δ ⊤

mutual
  data Val (Δ : Cx) : Ty → Set where
    ne   : ∀ {a}     (v : Ne Val Δ a)                 → Val Δ a
    lam  : ∀ {Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) → Val Δ (a ⇒ b)
    pair : ∀ {a b}   (v : Val Δ a)      (w : Val Δ b) → Val Δ (a ∧ b)
    unit :                                                Val Δ ⊤

  data Env (Δ : Cx) : Cx → Set where
    ∅   :                                         Env Δ ∅
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (w : Val Δ a) → Env Δ (Γ , a)




v₀ : ∀ {Γ a} → Tm (Γ , a) a
v₀ = var top

v₁ : ∀ {Γ a b} → Tm ((Γ , a) , b) a
v₁ = var (pop top)

v₂ : ∀ {Γ a b c} → Tm (((Γ , a) , b) , c) a
v₂ = var (pop (pop top))


nev₀ : ∀ {Δ a} → Val (Δ , a) a
nev₀ = ne (var top)
