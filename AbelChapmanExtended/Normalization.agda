module AbelChapmanExtended.Normalization where

open import Size using (∞)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.Renaming




lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup top     (γ , v) = v
lookup (pop x) (γ , v) = lookup x γ


mutual
  eval : ∀ {i Γ Δ b} → Tm Γ b → Env Δ Γ → Delay i (Val Δ b)
  eval (var x)    γ = now (lookup x γ)
  eval (lam t)    γ = now (lam t γ)
  eval (app t u)  γ = v ← eval t γ ⁏
                      w ← eval u γ ⁏
                      β-reduce v w
  eval unit       γ = now unit
  eval (pair t u) γ = v ← eval t γ ⁏
                      w ← eval u γ ⁏
                      now (pair v w)
  eval (fst t)    γ = v ← eval t γ ⁏
                      π₁-reduce v
  eval (snd t)    γ = v ← eval t γ ⁏
                      π₂-reduce v


  ∞eval : ∀ {i Γ Δ a} → Tm Γ a → Env Δ Γ → ∞Delay i (Val Δ a)
  force (∞eval t γ) = eval t γ


  β-reduce : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  β-reduce (ne v)    w = now (ne (app v w))
  β-reduce (lam t γ) w = later (∞eval t (γ , w))


  π₁-reduce : ∀ {i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ a)
  π₁-reduce (ne v)     = now (ne (fst v))
  π₁-reduce (pair v w) = now v


  π₂-reduce : ∀ {i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ b)
  π₂-reduce (ne v)     = now (ne (snd v))
  π₂-reduce (pair v w) = now w



mutual
  readback : ∀ {i Δ a} → Val Δ a → Delay i (Nf Δ a)
  readback {a = ★}      (ne v) = ne <$> readback-ne v
  readback {a = a ⇒ b} v      = later (∞η-expand v)
  readback {a = ⊤}     v      = now unit
  readback {a = a ∧ b}  v      = later (∞π-expand v)


  readback-ne : ∀ {i Δ a} → Ne Val Δ a → Delay i (Ne Nf Δ a)
  readback-ne (var x)   = now (var x)
  readback-ne (app v w) = n ← readback-ne v ⁏
                          m ← readback w ⁏
                          now (app n m)
  readback-ne (fst v)   = n ← readback-ne v ⁏
                          now (fst n)
  readback-ne (snd v)   = n ← readback-ne v ⁏
                          now (snd n)


  ∞η-expand : ∀ {i Δ a b} → Val Δ (a ⇒ b) → ∞Delay i (Nf Δ (a ⇒ b))
  force (∞η-expand v) = v′ ← β-reduce (ren-val (weak id) v) (ne (var top)) ⁏
                        n′ ← readback v′ ⁏
                        now (lam n′)


  ∞π-expand : ∀ {i Δ a b} → Val Δ (a ∧ b) → ∞Delay i (Nf Δ (a ∧ b))
  force (∞π-expand v) = v′ ← π₁-reduce v ⁏
                        w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′)


id-env : (Γ : Cx) → Env Γ Γ
id-env ∅       = ∅
id-env (Γ , a) = ren-env (weak id) (id-env Γ) , ne (var top)


nf? : ∀ {Γ a} → Tm Γ a → Delay ∞ (Nf Γ a)
nf? {Γ} t = t′ ← eval t (id-env Γ) ⁏
            readback t′
