module A201607.WIP.BasicILP.Sketch where

open import A201607.BasicILP.Syntax.DyadicGentzen hiding (dist ; up ; down)


{-
box : ∀ {Γ Δ Ψ Ω A}
    → (x : Ψ ⁏ Ω ⊢ A)
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A

unbox : ∀ {Γ Δ Ψ Ω A C x}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
    → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ C
    → Γ ⁏ Δ ⊢ C
-}


dist : ∀ {Γ Δ Ψ Ω A B x y}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] (A ▻ B)
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] A
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ app (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) ] B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))))))

up : ∀ {Γ Δ Ψ Ω A x}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ box (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆)) ] [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆) ] A
up t = unbox t (box (box (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆))))

down : ∀ {Γ Δ A x}
    → Γ ⁏ Δ ⊢ [ Γ ⁏ Δ ⊢ x ] A
    → Γ ⁏ Δ ⊢ A
down t = unbox t (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆))


module Test₁ where
  def₁ : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ A ∧ B ▻ B ∧ A
  def₁ = lam (pair (snd v₀) (fst v₀))

  def₀ : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ (A ∧ B) ∧ C
  def₀ = lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀)))

  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = lam (app def₁ (app def₀ v₀))

module Test₂ where
  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = let def₁ = lam (pair (snd v₀) (fst v₀)) in
         let def₀ = lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀))) in
             lam (app def₁ (app def₀ v₀))

module Test₃ where
  𝑙𝑒𝑡_𝑖𝑛_ : ∀ {Γ Δ A C}
      → (x : Γ ⁏ Δ ⊢ A)
      → Γ ⁏ Δ , [ Γ ⁏ Δ ⊢ x ] A ⊢ C
      → Γ ⁏ Δ ⊢ C
  𝑙𝑒𝑡 t 𝑖𝑛 u = unbox (box t) u

  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = 𝑙𝑒𝑡 lam (pair (snd v₀) (fst v₀)) 𝑖𝑛
         𝑙𝑒𝑡 lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀))) 𝑖𝑛
             lam (app (mv₁ (grefl⊢⋆ weak⊆) (gmrefl⊢⍟ (skip weak⊆))) (app (mv₀ (grefl⊢⋆ weak⊆) (gmrefl⊢⍟ weak⊆)) v₀))


ifvar : ∀ {Γ Δ Ψ Ω A x C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
    → Γ ⁏ Δ ⊢ C
ifvar s₁ s₂ (box (var i)) = s₁
ifvar s₁ s₂ t             = s₂

iflam : ∀ {Γ Δ Ψ Ω A B x C}
    → (∀ {t} → Γ ⁏ Δ ⊢ [ Ψ , A ⁏ Ω ⊢ t ] B ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] (A ▻ B)
    → Γ ⁏ Δ ⊢ C
iflam s₁ s₂ (box (lam t)) = app s₁ (box t)
iflam s₁ s₂ t             = s₂

ifapp : ∀ {Γ Δ Ψ Ω B x C}
    → (∀ {A y z} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] (A ▻ B) ▻ [ Ψ ⁏ Ω ⊢ z ] A ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] B
    → Γ ⁏ Δ ⊢ C
ifapp s₁ s₂ (box (app t u)) = app (app s₁ (box t)) (box u)
ifapp s₁ s₂ t               = s₂

ifpair : ∀ {Γ Δ Ψ Ω A B x C}
    → (∀ {y z} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] A ▻ [ Ψ ⁏ Ω ⊢ z ] B ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] (A ∧ B)
    → Γ ⁏ Δ ⊢ C
ifpair s₁ s₂ (box (pair t u)) = app (app s₁ (box t)) (box u)
ifpair s₁ s₂ t                = s₂

iffst : ∀ {Γ Δ Ψ Ω A x C}
    → (∀ {B y} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
    → Γ ⁏ Δ ⊢ C
iffst s₁ s₂ (box (fst t)) = app s₁ (box t)
iffst s₁ s₂ t             = s₂

ifsnd : ∀ {Γ Δ Ψ Ω B x C}
    → (∀ {A y} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] B
    → Γ ⁏ Δ ⊢ C
ifsnd s₁ s₂ (box (snd t)) = app s₁ (box t)
ifsnd s₁ s₂ t             = s₂

ifunit : ∀ {Γ Δ Ψ Ω x C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] ⊤
    → Γ ⁏ Δ ⊢ C
ifunit s₁ s₂ (box unit) = s₁
ifunit s₁ s₂ t          = s₂


-- NOTE: devar doesn’t seem desirable, as it would require an object-level representation
-- of variables and yield syntactic identity, while we want to retain α-equivalence.

delam : ∀ {Γ Δ Ψ Ω A B x}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ , A ⁏ Ω ⊢ x ] B ⊢ lam (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆)) ] (A ▻ B)
    → Γ ⁏ Δ ⊢ [ Ψ , A ⁏ Ω , [ Ψ , A ⁏ Ω ⊢ x ] B ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆) ] B
delam t = box (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆))

deapp₁ : ∀ {Γ Δ Ψ Ω A B x y}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ app (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) ] B
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)) ] (A ▻ B)
deapp₁ t = box (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)))

deapp₂ : ∀ {Γ Δ Ψ Ω A B x y}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ app (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) ] B
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)) ] A
deapp₂ t = box (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)))

depair₁ : ∀ {Γ Δ Ψ Ω A B x y}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ ⁏ Ω ⊢ y ] B ⊢ pair (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) ] (A ∧ B)
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ ⁏ Ω ⊢ y ] B ⊢ mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)) ] A
depair₁ t = box (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)))

depair₂ : ∀ {Γ Δ Ψ Ω A B x y}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ ⁏ Ω ⊢ y ] B ⊢ pair (mv₁ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆))) ] (A ∧ B)
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ ⁏ Ω ⊢ y ] B ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)) ] B
depair₂ t = box (mv₀ refl⊢⋆ (gmrefl⊢⍟ (skip weak⊆)))

defst : ∀ {Γ Δ Ψ Ω A B x}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ∧ B) ⊢ fst (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆)) ] A
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ∧ B) ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆) ] (A ∧ B)
defst t = box (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆))

desnd : ∀ {Γ Δ Ψ Ω A B x}
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ∧ B) ⊢ snd (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆)) ] B
    → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ∧ B) ⊢ mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆) ] (A ∧ B)
desnd t = box (mv₀ refl⊢⋆ (gmrefl⊢⍟ weak⊆))

-- NOTE: deunit doesn’t seem useful.
