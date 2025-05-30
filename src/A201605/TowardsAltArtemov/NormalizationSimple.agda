{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module A201605.TowardsAltArtemov.NormalizationSimple where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst)
open import Relation.Nullary using (Dec ; yes ; no)
open import Size using (∞)

open import A201605.AbelChapmanExtended.Delay
open import A201605.TowardsAltArtemov.SyntaxSimple


lookup : ∀ {Γ Δ A} → Var Γ A → Env Δ Γ → Val Δ A
lookup top     (γ , t) = t
lookup (pop x) (γ , t) = lookup x γ


-- TODO: unfinished
mutual
  eval : ∀ {i Γ Δ A} → Tm Γ A → Env Δ Γ → Delay i (Val Δ A)
  eval (var x)                   γ = now (lookup x γ)
  eval (lam⟨ n ⟩ {ts} t)         γ = now (lam⟨ n ⟩ {ts} t γ)
  eval (app⟨ n ⟩ {ts} {us} t u)  γ = v ← eval t γ ⁏ w ← eval u γ ⁏ {!β-reduce v w!}
  eval (pair⟨ n ⟩ {ts} {us} t u) γ = v ← eval t γ ⁏ w ← eval u γ ⁏ now (pair⟨ n ⟩ {ts} {us} v w)
  eval (fst⟨ n ⟩ {ts} t)         γ = v ← eval t γ ⁏ {!π₁-reduce v!}
  eval (snd⟨ n ⟩ {ts} t)         γ = v ← eval t γ ⁏ {!π₂-reduce v!}
  eval (up⟨ n ⟩ {ts} t)          γ = v ← eval t γ ⁏ now (up⟨ n ⟩ {ts} v)
  eval (down⟨ n ⟩ {ts} t)        γ = v ← eval t γ ⁏ {!δ-reduce v!}

  ∞eval : ∀ {i Γ Δ A} → Tm Γ A → Env Δ Γ → ∞Delay i (Val Δ A)
  force (∞eval t γ) = eval t γ

  β-reduce : ∀ {i Δ n} {ts us : Vec n} {A B} → Val Δ (ts ∴ (A ⊃ B)) → Val Δ (us ∴ A) → Delay i (Val Δ (°apps⟨ n ⟩ ts us ∴ B))
  β-reduce = {!!}
  --β-reduce (ne v)    w = now (ne (app v w))
  --β-reduce (lam t γ) w = later (∞eval t (γ , w))

  π₁-reduce : ∀ {i Δ n} {ts : Vec n} {A B} → Val Δ (ts ∴ (A ∧ B)) → Delay i (Val Δ (°fsts⟨ n ⟩ ts ∴ A))
  π₁-reduce = {!!}
  --π₁-reduce (ne v)     = now (ne (fst v))
  --π₁-reduce (pair v w) = now v

  π₂-reduce : ∀ {i Δ n} {ts : Vec n} {A B} → Val Δ (ts ∴ (A ∧ B)) → Delay i (Val Δ (°snds⟨ n ⟩ ts ∴ B))
  π₂-reduce = {!!}
  --π₂-reduce (ne v)     = now (ne (snd v))
  --π₂-reduce (pair v w) = now w
