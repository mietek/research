module AbelChapmanExtended.Renaming.Normalization1 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.StrongBisimilarity

open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.Renaming.Syntax
open import AbelChapmanExtended.Normalization




ren-lookup : ∀ {Γ Δ Δ′ a} (η : Δ′ ⊇ Δ) (x : Var Γ a) (ρ : Env Δ Γ) →
             ren-val η (lookup x ρ) ≡ lookup x (ren-env η ρ)
ren-lookup η top     (ρ , v) = refl
ren-lookup η (pop x) (ρ , v) = ren-lookup η x ρ


ren-π₁-reduce : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∧ b)) →
                ren-val η <$> π₁-reduce v ≈⟨ i ⟩≈ π₁-reduce (ren-val η v)
ren-π₁-reduce η (ne v)     = ≈refl
ren-π₁-reduce η (pair v w) = ≈refl


ren-π₂-reduce : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∧ b)) →
                ren-val η <$> π₂-reduce v ≈⟨ i ⟩≈ π₂-reduce (ren-val η v)
ren-π₂-reduce η (ne v)     = ≈refl
ren-π₂-reduce η (pair v w) = ≈refl


ren-ω-reduce : ∀ {i Δ Δ′ a} (η : Δ′ ⊇ Δ) (v : Val Δ ⊥) →
               ren-val η <$> ω-reduce v ≈⟨ i ⟩≈ ω-reduce {a = a} (ren-val η v)
ren-ω-reduce η (ne v)     = ≈refl


mutual
  ren-eval : ∀ {i Γ Δ Δ′ a} (η : Δ′ ⊇ Δ) (t : Tm Γ a) (ρ : Env Δ Γ) →
             ren-val η <$> eval t ρ ≈⟨ i ⟩≈ eval t (ren-env η ρ)
  ren-eval η (loop t) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         ω-reduce v)
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> ω-reduce v
    ≈⟨ v ⇚ eval t ρ ⁏
       ren-ω-reduce η v ⟩
          v ← eval t ρ ⁏
          ω-reduce (ren-val η v)
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          ω-reduce v′
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          ω-reduce v′
    ∎
    where open ≈-Reasoning
  ren-eval η (var x)   ρ rewrite ren-lookup η x ρ = ≈now (lookup x (ren-env η ρ))
  ren-eval η (lam t)   ρ = ≈now (lam t (ren-env η ρ))
  ren-eval η (app t u) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         w ← eval u ρ ⁏
                         β-reduce v w)
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> (w ← eval u ρ ⁏
                         β-reduce v w)
    ≈⟨ v ⇚ eval t ρ ⁏
       ⋘ eval u ρ ⟩
          v ← eval t ρ ⁏
          w ← eval u ρ ⁏
          ren-val η <$> β-reduce v w
    ≈⟨ v ⇚ eval t ρ ⁏
       w ⇚ eval u ρ ⁏
       ren-β-reduce η v w ⟩
          v ← eval t ρ ⁏
          w ← eval u ρ ⁏
          β-reduce (ren-val η v) (ren-val η w)
    ≈⟨ v ⇚ eval t ρ ⁏
       ⋙ eval u ρ ⟩
          v  ← eval t ρ ⁏
          w′ ← ren-val η <$> eval u ρ ⁏
          β-reduce (ren-val η v) w′
    ≈⟨ v ⇚ eval t ρ ⁏
       ∵ ren-eval η u ρ ⟩
          v  ← eval t ρ ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          β-reduce (ren-val η v) w′
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          β-reduce v′ w′
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          β-reduce v′ w′
    ∎
    where open ≈-Reasoning
  ren-eval η (pair t u) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         w ← eval u ρ ⁏
                         now (pair v w))
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> (w ← eval u ρ ⁏
                         now (pair v w))
    ≈⟨ v ⇚ eval t ρ ⁏
       ⋘ eval u ρ ⟩
          v ← eval t ρ ⁏
          w ← eval u ρ ⁏
          ren-val η <$> now (pair v w)
    ≈⟨ v ⇚ eval t ρ ⁏
       w ⇚ eval u ρ ⁏
       ≈now (pair (ren-val η v) (ren-val η w)) ⟩
          v ← eval t ρ ⁏
          w ← eval u ρ ⁏
          now (pair (ren-val η v) (ren-val η w))
    ≈⟨ v ⇚ eval t ρ ⁏
       ⋙ eval u ρ ⟩
          v  ← eval t ρ ⁏
          w′ ← ren-val η <$> eval u ρ ⁏
          now (pair (ren-val η v) w′)
    ≈⟨ v ⇚ eval t ρ ⁏
       ∵ ren-eval η u ρ ⟩
          v  ← eval t ρ ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          now (pair (ren-val η v) w′)
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          now (pair v′ w′)
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          w′ ← eval u (ren-env η ρ) ⁏
          now (pair v′ w′)
    ∎
    where open ≈-Reasoning
  ren-eval η (fst t) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         π₁-reduce v)
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> π₁-reduce v
    ≈⟨ v ⇚ eval t ρ ⁏
       ren-π₁-reduce η v ⟩
          v ← eval t ρ ⁏
          π₁-reduce (ren-val η v)
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          π₁-reduce v′
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          π₁-reduce v′
    ∎
    where open ≈-Reasoning
  ren-eval η (snd t) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         π₂-reduce v)
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> π₂-reduce v
    ≈⟨ v ⇚ eval t ρ ⁏
       ren-π₂-reduce η v ⟩
          v ← eval t ρ ⁏
          π₂-reduce (ren-val η v)
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          π₂-reduce v′
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          π₂-reduce v′
    ∎
    where open ≈-Reasoning
  ren-eval η unit ρ = ≈now unit


  ren-∞eval : ∀ {i Γ Δ Δ′ a} (η : Δ′ ⊇ Δ) (t : Tm Γ a) (ρ : Env Δ Γ) →
              ren-val η ∞<$> ∞eval t ρ ∞≈⟨ i ⟩≈ ∞eval t (ren-env η ρ)
  ≈force (ren-∞eval η t ρ) = ren-eval η t ρ


  ren-β-reduce : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ⇒ b)) (w : Val Δ a) →
                 ren-val η <$> β-reduce v w ≈⟨ i ⟩≈ β-reduce (ren-val η v) (ren-val η w)
  ren-β-reduce η (ne v)    w = ≈refl
  ren-β-reduce η (lam t ρ) w = ≈later (ren-∞eval η t (ρ , w))
