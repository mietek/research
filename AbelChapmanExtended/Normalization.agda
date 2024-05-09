module AbelChapmanExtended.Normalization where

open import Size using (∞)

open import AbelChapmanExtended.Delay

open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.Renaming.Syntax




lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup top     (ρ , v) = v
lookup (pop x) (ρ , v) = lookup x ρ

ω-reduce : ∀ {i Δ a} → Val Δ ⊥ → Delay i (Val Δ a)
ω-reduce (ne v) = now (ne (loop v))

π₁-reduce : ∀ {i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ a)
π₁-reduce (ne v)     = now (ne (fst v))
π₁-reduce (pair v w) = now v

π₂-reduce : ∀ {i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ b)
π₂-reduce (ne v)     = now (ne (snd v))
π₂-reduce (pair v w) = now w


mutual
  eval : ∀ {i Γ Δ b} → Tm Γ b → Env Δ Γ → Delay i (Val Δ b)
  eval (loop t)   ρ = v ← eval t ρ ⁏
                      ω-reduce v
  eval (var x)    ρ = now (lookup x ρ)
  eval (lam t)    ρ = now (lam t ρ)
  eval (app t u)  ρ = v ← eval t ρ ⁏
                      w ← eval u ρ ⁏
                      β-reduce v w
  eval (pair t u) ρ = v ← eval t ρ ⁏
                      w ← eval u ρ ⁏
                      now (pair v w)
  eval (fst t)    ρ = v ← eval t ρ ⁏
                      π₁-reduce v
  eval (snd t)    ρ = v ← eval t ρ ⁏
                      π₂-reduce v
  eval unit       ρ = now unit

  ∞eval : ∀ {i Γ Δ a} → Tm Γ a → Env Δ Γ → ∞Delay i (Val Δ a)
  force (∞eval t ρ) = eval t ρ

  β-reduce : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  β-reduce (ne v)    w = now (ne (app v w))
  β-reduce (lam t ρ) w = later (∞eval t (ρ , w))


mutual
  readback : ∀ {i Δ a} → Val Δ a → Delay i (Nf Δ a)
  readback {a = ⊥}     (ne v) = ne <$> readback-ne v
  readback {a = a ⇒ b} v      = later (∞η-expand v)
  readback {a = a ∧ b}  v      = later (∞ψ-expand v)
  readback {a = ⊤}     v      = now unit

  readback-ne : ∀ {i Δ a} → Ne Val Δ a → Delay i (Ne Nf Δ a)
  readback-ne (loop v)  = n ← readback-ne v ⁏
                          now (loop n)
  readback-ne (var x)   = now (var x)
  readback-ne (app v w) = n ← readback-ne v ⁏
                          m ← readback w ⁏
                          now (app n m)
  readback-ne (fst v)   = n ← readback-ne v ⁏
                          now (fst n)
  readback-ne (snd v)   = n ← readback-ne v ⁏
                          now (snd n)

  ∞η-expand : ∀ {i Δ a b} → Val Δ (a ⇒ b) → ∞Delay i (Nf Δ (a ⇒ b))
  force (∞η-expand v) = v′ ← β-reduce (wk-val v) nev₀ ⁏
                        n′ ← readback v′ ⁏
                        now (lam n′)

  ∞ψ-expand : ∀ {i Δ a b} → Val Δ (a ∧ b) → ∞Delay i (Nf Δ (a ∧ b))
  force (∞ψ-expand v) = v′ ← π₁-reduce v ⁏
                        w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′)


id-env : (Γ : Cx) → Env Γ Γ
id-env ∅       = ∅
id-env (Γ , a) = (ren-env wk (id-env Γ) , nev₀)

nf? : ∀ {Γ a} → Tm Γ a → Delay ∞ (Nf Γ a)
nf? {Γ} t = t′ ← eval t (id-env Γ) ⁏
            readback t′
