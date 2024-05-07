{-# OPTIONS --allow-unsolved-metas #-}

module A201607.WIP.BasicIS4.Sketch where

open import A201607.BasicIS4.Syntax.DyadicGentzen hiding (dist ; up ; down)


{-
box : ∀ {Γ Δ A}
    → ∅ ⁏ Δ ⊢ A
    → Γ ⁏ Δ ⊢ □ A

unbox : ∀ {Γ Δ A C}
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ , A ⊢ C
    → Γ ⁏ Δ ⊢ C
-}


dist : ∀ {Γ Δ A B}
    → Γ ⁏ Δ ⊢ □ (A ▻ B)
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ ⊢ □ B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app mv₁ mv₀)))

up : ∀ {Γ Δ A}
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ ⊢ □ □ A
up t = unbox t (box (box mv₀))

down : ∀ {Γ Δ A}
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ ⊢ A
down t = unbox t mv₀


module Test₁ where
  def₁ : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ A ∧ B ▻ B ∧ A
  def₁ = lam (pair (snd v₀) (fst v₀))

  def₀ : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ (A ∧ B) ∧ C
  def₀ = lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀)))

  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = lam (app def₁ (app def₀ v₀))

  dup : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A ▻ A ∧ A
  dup = lam (pair v₀ v₀)

  test′ : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ A ∧ B ▻ (A ∧ A) ∧ (B ∧ B)
  test′ = lam (pair (app dup (fst v₀)) (app dup (snd v₀)))

module Test₂ where
  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = let def₁ = lam (pair (snd v₀) (fst v₀)) in
         let def₀ = lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀))) in
             lam (app def₁ (app def₀ v₀))

--  test′ : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ A ∧ B ▻ (A ∧ A) ∧ (B ∧ B)
--  test′ = let dup = lam (pair v₀ v₀) in
--              lam (pair (app dup (fst v₀)) (app dup (snd v₀)))

module Test₃ where
  𝑙𝑒𝑡_𝑖𝑛_ : ∀ {Γ Δ A C}
      → ∅ ⁏ Δ ⊢ A
      → Γ ⁏ Δ , A ⊢ C
      → Γ ⁏ Δ ⊢ C
  𝑙𝑒𝑡 t 𝑖𝑛 u = unbox (box t) u

  test : ∀ {Γ Δ A B C} → Γ ⁏ Δ ⊢ A ∧ (B ∧ C) ▻ C ∧ (A ∧ B)
  test = 𝑙𝑒𝑡 lam (pair (snd v₀) (fst v₀)) 𝑖𝑛
         𝑙𝑒𝑡 lam (pair (pair (fst v₀) (fst (snd v₀))) (snd (snd v₀))) 𝑖𝑛
             lam (app mv₁ (app mv₀ v₀))

  -- TODO: unfinished
  test′ : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ A ∧ B ▻ (A ∧ A) ∧ (B ∧ B)
  test′ = 𝑙𝑒𝑡 lam (pair v₀ v₀) 𝑖𝑛
          lam (pair (app mv₀ (fst v₀)) (app {!mv₀!} (snd v₀)))




ifvar : ∀ {Γ Δ A C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ ⊢ C
ifvar s₁ s₂ (box (var i)) = s₁
ifvar s₁ s₂ t             = s₂

-- NOTE: iflam is impossible without being able to quote open terms.

-- iflam : ∀ {Γ Δ A B C}
--     → Γ ⁏ Δ ⊢ {![ ∅ , A ]!} B ▻ C
--     → Γ ⁏ Δ ⊢ C
--     → Γ ⁏ Δ ⊢ □ (A ▻ B)
--     → Γ ⁏ Δ ⊢ C
-- iflam s₁ s₂ (box (lam t)) = app s₁ (box t)
-- iflam s₁ s₂ t             = s₂

ifapp : ∀ {Γ Δ B C}
    → (∀ {A} → Γ ⁏ Δ ⊢ □ (A ▻ B) ▻ □ A ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ B
    → Γ ⁏ Δ ⊢ C
ifapp s₁ s₂ (box (app t u)) = app (app s₁ (box t)) (box u)
ifapp s₁ s₂ t               = s₂

ifpair : ∀ {Γ Δ A B C}
    → Γ ⁏ Δ ⊢ □ A ▻ □ B ▻ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ (A ∧ B)
    → Γ ⁏ Δ ⊢ C
ifpair s₁ s₂ (box (pair t u)) = app (app s₁ (box t)) (box u)
ifpair s₁ s₂ t                = s₂

iffst : ∀ {Γ Δ A C}
    → (∀ {B} → Γ ⁏ Δ ⊢ □ (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ A
    → Γ ⁏ Δ ⊢ C
iffst s₁ s₂ (box (fst t)) = app s₁ (box t)
iffst s₁ s₂ t             = s₂

ifsnd : ∀ {Γ Δ B C}
    → (∀ {A} → Γ ⁏ Δ ⊢ □ (A ∧ B) ▻ C)
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ B
    → Γ ⁏ Δ ⊢ C
ifsnd s₁ s₂ (box (snd t)) = app s₁ (box t)
ifsnd s₁ s₂ t             = s₂

ifunit : ∀ {Γ Δ C}
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ C
    → Γ ⁏ Δ ⊢ □ ⊤
    → Γ ⁏ Δ ⊢ C
ifunit s₁ s₂ (box unit) = s₁
ifunit s₁ s₂ t          = s₂
