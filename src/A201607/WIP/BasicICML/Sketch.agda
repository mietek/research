{-# OPTIONS --sized-types #-}

module A201607.WIP.BasicICML.Sketch where

open import A201607.BasicICML.Syntax.DyadicGentzen hiding (dist ; up ; down)


{-
box : ∀ {Γ Δ Ψ A}
    → Ψ ⁏ Δ ⊢ A
    → Γ ⁏ Δ ⊢ [ Ψ ] A

unbox : ∀ {Γ Δ Ψ A C}
    → Γ ⁏ Δ ⊢ [ Ψ ] A
    → Γ ⁏ Δ , [ Ψ ] A ⊢ C
    → Γ ⁏ Δ ⊢ C
-}


dist : ∀ {Γ Δ Ψ A B}
    → Γ ⁏ Δ ⊢ [ Ψ ] (A ▻ B)
    → Γ ⁏ Δ ⊢ [ Ψ ] A
    → Γ ⁏ Δ ⊢ [ Ψ ] B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app (mv₁ refl⊢⋆) (mv₀ refl⊢⋆))))

up : ∀ {Γ Δ Ψ A}
    → Γ ⁏ Δ ⊢ [ Ψ ] A
    → Γ ⁏ Δ ⊢ [ Ψ ] [ Ψ ] A
up t = unbox t (box (box (mv₀ refl⊢⋆)))

down : ∀ {Γ Δ A}
    → Γ ⁏ Δ ⊢ [ Γ ] A
    → Γ ⁏ Δ ⊢ A
down t = unbox t (mv₀ refl⊢⋆)


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
      → Γ ⁏ Δ ⊢ A
      → Γ ⁏ Δ , [ Γ ] A ⊢ C
      → Γ ⁏ Δ ⊢ C
  𝑙𝑒𝑡 t 𝑖𝑛 u = unbox (box t) u

  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = 𝑙𝑒𝑡 lam (pair (snd v₀) (fst v₀)) 𝑖𝑛
         𝑙𝑒𝑡 lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀))) 𝑖𝑛
             lam (app (mv₁ (grefl⊢⋆ weak⊆)) (app (mv₀ (grefl⊢⋆ weak⊆)) v₀))


ifvar : ∀ {Γ Δ Ψ A C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] A
    → Γ ⁏ Δ ⊢ C
ifvar s₁ s₂ (box (var i)) = s₁
ifvar s₁ s₂ t             = s₂

iflam : ∀ {Γ Δ Ψ A B C}
    → Γ ⁏ Δ ⊢ [ Ψ , A ] B ▻ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] (A ▻ B)
    → Γ ⁏ Δ ⊢ C
iflam s₁ s₂ (box (lam t)) = app s₁ (box t)
iflam s₁ s₂ t             = s₂

ifapp : ∀ {Γ Δ Ψ B C}
    → (∀ {A} → Γ ⁏ Δ ⊢ [ Ψ ] (A ▻ B) ▻ [ Ψ ] A ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] B
    → Γ ⁏ Δ ⊢ C
ifapp s₁ s₂ (box (app t u)) = app (app s₁ (box t)) (box u)
ifapp s₁ s₂ t               = s₂

ifpair : ∀ {Γ Δ Ψ A B C}
    → Γ ⁏ Δ ⊢ [ Ψ ] A ▻ [ Ψ ] B ▻ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] (A ∧ B)
    → Γ ⁏ Δ ⊢ C
ifpair s₁ s₂ (box (pair t u)) = app (app s₁ (box t)) (box u)
ifpair s₁ s₂ t                = s₂

iffst : ∀ {Γ Δ Ψ A C}
    → (∀ {B} → Γ ⁏ Δ ⊢ [ Ψ ] (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] A
    → Γ ⁏ Δ ⊢ C
iffst s₁ s₂ (box (fst t)) = app s₁ (box t)
iffst s₁ s₂ t             = s₂

ifsnd : ∀ {Γ Δ Ψ B C}
    → (∀ {A} → Γ ⁏ Δ ⊢ [ Ψ ] (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] B
    → Γ ⁏ Δ ⊢ C
ifsnd s₁ s₂ (box (snd t)) = app s₁ (box t)
ifsnd s₁ s₂ t             = s₂

ifunit : ∀ {Γ Δ Ψ C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ [ Ψ ] ⊤
    → Γ ⁏ Δ ⊢ C
ifunit s₁ s₂ (box unit) = s₁
ifunit s₁ s₂ t          = s₂
