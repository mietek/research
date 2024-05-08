module A201607.WIP2.BasicICML.Sketch where

open import A201607.BasicICML.Syntax.DyadicGentzen public


-- Let us assume some types X and Y, and a function foo from X to Y.
postulate
  X : Ty
  Y : Ty
  foo : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ X ▻ Y

-- We can construct a term of type Y under the assumption that we have a term of type X.
-- In other words, we can construct a term with a free variable, or an open term.
a1 : ∀ {Γ Δ} → Γ , X ⁏ Δ ⊢ Y
a1 = app foo v₀

-- We can also construct a term of type Y under the assumption that we have a quoted term of type X.
-- In other words, we can construct a term with a free metavariable.
a2 : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] X ⊢ Y
a2 = app foo (mv₀ ∙)

-- We can quote terms with free variables, because we track free variables in the type.
b1 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ , X ] Y
b1 = box (app foo v₀)

-- We can also quote terms with free metavariables, as long as we can supply these metavariables.
b2 : ∀ {Γ Δ} → Γ ⁏ Δ , [ ∅ ] X ⊢ [ ∅ ] Y
b2 = box (app foo (mv₀ ∙))


-- Now, let us assume a value of type X.
postulate
  bar : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ X

-- To construct a term of type Y, we can apply foo directly.
c1 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ Y
c1 = app foo bar

-- We can also close the open term and apply the result.
c2 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ Y
c2 = app (lam a1) bar

-- We can also bind a metavariable to our value of type X.
-- This could be a way to implement let-bindings.
-- Note that the
c3 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ Y
c3 = unbox {Ψ = ∅} (box bar) (app foo (mv₀ ∙))

-- We can simply quote a closed term.
d1 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] Y
d1 = box (app foo bar)

d2 : ∀ {Γ Δ} → Γ ⁏ Δ ⊢ [ ∅ ] Y
d2 = unbox {Ψ = ∅} (box bar) (box (app foo (mv₀ ∙)))
