module A201607.WIP.Sketch where

open import A201607.BasicIS4.Syntax.DyadicGentzen



-- Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ □ A ▻ □ B


-- fmap : ∀ {Γ Δ A B} → ∅ ⁏ Δ ⊢ (A ▻ B) ▻ □ A ▻ □ B
-- fmap = lam (lam {!𝑞𝑢𝑜𝑡𝑒 v₁!})

-- ((¬¬A → A) → (A ∨ ¬A)) → (¬A ∨ ¬¬A)


-- -- cfmap : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ (A → B) → □ A → □ B
-- -- cfmap = {!!}

-- -- fmap : ∀ {

-- -- ccounit : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ □ A ▻ A
-- -- ccounit = cdown

-- -- (□ A → B) → □ A → □ B

-- -- ccobind : ∀ {Γ Δ A B} → Γ ⁏ Δ ⊢ (□ A ▻ B) ▻ □ A ▻ □ B
-- -- ccobind = lam (lam (app (app cfmap v₁) (up v₀)))

-- -- box : ∀ {Γ Δ A} → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A

-- -- multibox : ∀ {Γ Ξ A} → Γ ⊢⋆ □⋆ Ξ → □⋆ Ξ ⊢ A → Γ ⊢ □ A
