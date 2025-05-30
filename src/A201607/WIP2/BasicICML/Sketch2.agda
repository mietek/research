{-# OPTIONS --sized-types #-}

module A201607.WIP2.BasicICML.Sketch2 where

open import A201607.BasicICML.Syntax.DyadicGentzen hiding (ℕ ; 𝟘 ; 𝟙) public

infixl 3 _+_
postulate
  ℕ : Ty
  𝟘 𝟙 𝟚 𝟛 𝟞 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ ℕ
  _+_ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ ℕ → Γ ⁏ Δ ⊢ ℕ → Γ ⁏ Δ ⊢ ℕ

-- Let’s say we have a simple expression referencing a free variable.

e₁ : ∀ {Γ Δ} → Γ , ℕ ⁏ Δ ⊢ ℕ
e₁ = 𝟙 + 𝟚 + v₀

-- We can partially normalise the expression without having to substitute the
-- variable away.

ne₁ : ∀ {Γ Δ} → Γ , ℕ ⁏ Δ ⊢ ℕ
ne₁ = 𝟛 + v₀

-- In ICML, we can quote expressions with free variables.  Therefore, if we can
-- check quoted expressions for α-equivalence, we can distinguish between the
-- original and the partially-normalised version of the expression.

qe₁ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ , ℕ ] ℕ
qe₁ = box (𝟙 + 𝟚 + v₀)

qne₁ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ , ℕ ] ℕ
qne₁ = box (𝟛 + v₀)

-- We can also consider the free variable as a reference to a previously
-- introduced definition, by replacing it with a free meta-variable.

e₂ : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] ℕ ⊢ ℕ
e₂ = 𝟙 + 𝟚 + mv₀ ∙

ne₂ : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] ℕ ⊢ ℕ
ne₂ = 𝟛 + mv₀ ∙

-- TODO: Unclear whether free meta-variables should or should not be listed in
-- the type of quoted expressions.

qe₂ : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] ℕ ⊢ [ ∅ ] ℕ
qe₂ = box (𝟙 + 𝟚 + mv₀ ∙)

qne₂ : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] ℕ ⊢ [ ∅ ] ℕ
qne₂ = box (𝟛 + mv₀ ∙)

-- Let’s say we have previously introduced a definition of 3, and we want to
-- reference it in our expression in a manner similar to let-binding, that is:
--   let three = 3 in 1 + 2 + three

e₃ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ ℕ
e₃ = unbox {Ψ = ∅} (box 𝟛) (𝟙 + 𝟚 + mv₀ ∙)

ne₃ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ ℕ
ne₃ = unbox {Ψ = ∅} (box 𝟛) (𝟛 + mv₀ ∙)

qe₃ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] ℕ
qe₃ = unbox {Ψ = ∅} (box 𝟛) (box (𝟙 + 𝟚 + mv₀ ∙))

qne₃ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] ℕ
qne₃ = unbox {Ψ = ∅} (box 𝟛) (box (𝟛 + mv₀ ∙))

-- Now, we can achieve the expected result of splicing by performing one step
-- of reduction, or meta-variable substitution.

qe₄ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] ℕ
qe₄ = box (𝟙 + 𝟚 + 𝟛)

qne₄ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] ℕ
qne₄ = box (𝟛 + 𝟛)

-- Both of the above quoted expressions are nevertheless different from what we
-- would get by normalising before quoting (box-val).

qe₅ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] ℕ
qe₅ = box 𝟞
