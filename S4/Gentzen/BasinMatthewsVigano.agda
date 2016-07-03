module S4.Gentzen.BasinMatthewsVigano where

open import S4.Core public


-- Labels, as in Gabbay’s labelled deductive systems (LDS).

postulate
  La : Set


-- Accessibility relation of S4, following Basin, Matthews, and Viganò.

infix 1 _⊢_≤_
data _⊢_≤_ (Ξ : Cx (La × La)) : La → La → Set where
  rvar   : ∀ {x y} → x ∙ y ∈ Ξ → Ξ ⊢ x ≤ y
  rrefl  : ∀ {x} → Ξ ⊢ x ≤ x
  rtrans : ∀ {x y z} → Ξ ⊢ x ≤ y → Ξ ⊢ y ≤ z → Ξ ⊢ x ≤ z


-- Proofs of S4, as labelled Gentzen-style natural deduction trees, following Basin, Matthews, and Viganò.

infix 1 _⨾_⊢_⦂_
data _⨾_⊢_⦂_ (Γ : Cx (La × Ty)) (Ξ : Cx (La × La)) : La → Ty → Set where
  var  : ∀ {x A}     → x ∙ A ∈ Γ → Γ ⨾ Ξ ⊢ x ⦂ A
  lam  : ∀ {x A B}   → Γ , x ∙ A ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ B
  app  : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ B → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ x ⦂ B
  nec  : ∀ {x A}     → (∀ {y} → Γ ⨾ Ξ , x ∙ y ⊢ y ⦂ A) → Γ ⨾ Ξ ⊢ x ⦂ □ A
  down : ∀ {x y A}   → Γ ⨾ Ξ ⊢ x ⦂ □ A → Ξ ⊢ x ≤ y → Γ ⨾ Ξ ⊢ y ⦂ A
  pair : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B
  fst  : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B → Γ ⨾ Ξ ⊢ x ⦂ A
  snd  : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B → Γ ⨾ Ξ ⊢ x ⦂ B
  inl  : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ x ⦂ A ∨ B
  inr  : ∀ {x A B}   → Γ ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ∨ B
  case : ∀ {x A B C} → Γ ⨾ Ξ ⊢ x ⦂ A ∨ B → Γ , x ∙ A ⨾ Ξ ⊢ x ⦂ C → Γ , x ∙ B ⨾ Ξ ⊢ x ⦂ C → Γ ⨾ Ξ ⊢ x ⦂ C
  boom : ∀ {x C}     → Γ ⨾ Ξ ⊢ x ⦂ ⊥ → Γ ⨾ Ξ ⊢ x ⦂ C


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢ : ∀ {x A Γ Γ′ Ξ} → Γ ⊆ Γ′ → Γ ⨾ Ξ ⊢ x ⦂ A → Γ′ ⨾ Ξ ⊢ x ⦂ A
mono⊢ η (var i)      = var (mono∈ η i)
mono⊢ η (lam t)      = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)    = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (nec t)      = nec (mono⊢ η t)
mono⊢ η (down t u)   = down (mono⊢ η t) u
mono⊢ η (pair t u)   = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)      = fst (mono⊢ η t)
mono⊢ η (snd t)      = snd (mono⊢ η t)
mono⊢ η (inl t)      = inl (mono⊢ η t)
mono⊢ η (inr t)      = inr (mono⊢ η t)
mono⊢ η (case t u v) = case (mono⊢ η t) (mono⊢ (keep η) u) (mono⊢ (keep η) v)
mono⊢ η (boom t)     = boom (mono⊢ η t)


-- Monotonicity of syntactic consequence with respect to relational context extension.

rmono⊢≤ : ∀ {x y Ξ Ξ′} → Ξ ⊆ Ξ′ → Ξ ⊢ x ≤ y → Ξ′ ⊢ x ≤ y
rmono⊢≤ η (rvar i)     = rvar (mono∈ η i)
rmono⊢≤ η rrefl        = rrefl
rmono⊢≤ η (rtrans t u) = rtrans (rmono⊢≤ η t) (rmono⊢≤ η u)

rmono⊢ : ∀ {x A Γ Ξ Ξ′} → Ξ ⊆ Ξ′ → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ′ ⊢ x ⦂ A
rmono⊢ η (var i)      = var i
rmono⊢ η (lam t)      = lam (rmono⊢ η t)
rmono⊢ η (app t u)    = app (rmono⊢ η t) (rmono⊢ η u)
rmono⊢ η (nec t)      = nec (rmono⊢ (keep η) t)
rmono⊢ η (down t u)   = down (rmono⊢ η t) (rmono⊢≤ η u)
rmono⊢ η (pair t u)   = pair (rmono⊢ η t) (rmono⊢ η u)
rmono⊢ η (fst t)      = fst (rmono⊢ η t)
rmono⊢ η (snd t)      = snd (rmono⊢ η t)
rmono⊢ η (inl t)      = inl (rmono⊢ η t)
rmono⊢ η (inr t)      = inr (rmono⊢ η t)
rmono⊢ η (case t u v) = case (rmono⊢ η t) (rmono⊢ η u) (rmono⊢ η v)
rmono⊢ η (boom t)     = boom (rmono⊢ η t)


-- Shorthand for variables.

rv₀ : ∀ {x y Ξ} → Ξ , x ∙ y ⊢ x ≤ y
rv₀ = rvar top

rv₁ : ∀ {x y x′ y′ Ξ} → Ξ , x ∙ y , x′ ∙ y′ ⊢ x ≤ y
rv₁ = rvar (pop top)

rv₂ : ∀ {x y x′ y′ x″ y″ Ξ} → Ξ , x ∙ y , x′ ∙ y′ , x″ ∙ y″ ⊢ x ≤ y
rv₂ = rvar (pop (pop top))

v₀ : ∀ {x A Γ Ξ} → Γ , x ∙ A ⨾ Ξ ⊢ x ⦂ A
v₀ = var top

v₁ : ∀ {x y A B Γ Ξ} → Γ , x ∙ A , y ∙ B ⨾ Ξ ⊢ x ⦂ A
v₁ = var (pop top)

v₂ : ∀ {x y z A B C Γ Ξ} → Γ , x ∙ A , y ∙ B , z ∙ C ⨾ Ξ ⊢ x ⦂ A
v₂ = var (pop (pop top))


-- Deduction theorem.

ded : ∀ {x A B Γ Ξ} → Γ , x ∙ A ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ B
ded t = lam t


-- TODO: Modal deduction theorem.


-- Useful theorems in combinatory form.

ci : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ A
ci = lam v₀

ck : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ B ⇒ A
ck = lam (lam v₁)

cs : ∀ {x A B C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (A ⇒ B) ⇒ □ A ⇒ □ B
cdist = lam (lam (nec (app (down v₁ rv₀) (down v₀ rv₀))))

cup : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A ⇒ □ □ A
cup = lam (nec (nec (down v₀ (rtrans rv₁ rv₀))))

cdown : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A ⇒ A
cdown = lam (down v₀ rrefl)

cdistup : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (□ A ⇒ B) ⇒ □ A ⇒ □ B
cdistup = lam (lam (app (app cdist v₁) (app cup v₀)))

cpair : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ B ⇒ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B ⇒ A
cfst = lam (fst v₀)

csnd : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B ⇒ B
csnd = lam (snd v₀)

cinl : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⇒ A ∨ B
cinl = lam (inl v₀)

cinr : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ B ⇒ A ∨ B
cinr = lam (inr v₀)

ccase : ∀ {x A B C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
ccase = lam (lam (lam (case v₂ (app v₂ v₀) (app v₁ v₀))))

cboom : ∀ {x C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ ⊥ ⇒ C
cboom = lam (boom v₀)
