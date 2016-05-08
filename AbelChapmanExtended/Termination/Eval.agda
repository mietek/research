module AbelChapmanExtended.Termination.Eval where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.StrongBisimilarity
open import AbelChapmanExtended.Syntax




mutual
  ren-lookup : ∀ {Γ Δ Δ′ a} (ρ : Δ′ ≥ Δ) (x : Var Γ a) (γ : Env Δ Γ) →
               ren-val ρ (lookup x γ) ≡ lookup x (ren-env ρ γ)
  ren-lookup ρ top     (γ , v) = refl
  ren-lookup ρ (pop x) (γ , v) = ren-lookup ρ x γ


  ren-eval : ∀ {i Γ Δ Δ′ a} (ρ : Δ′ ≥ Δ) (t : Tm Γ a) (γ : Env Δ Γ) →
             ren-val ρ <$> eval t γ ≈⟨ i ⟩≈ eval t (ren-env ρ γ)
  ren-eval ρ (var x)   γ rewrite ren-lookup ρ x γ = ≈now (lookup x (ren-env ρ γ))
  ren-eval ρ (lam t)   γ = ≈now (lam t (ren-env ρ γ))
  ren-eval ρ (app t u) γ =
    proof
          ren-val ρ <$> (v ← eval t γ ⁏
                         w ← eval u γ ⁏
                         β-reduce v w)
    ≈⟨ ⮦ eval t γ ⟩
          v ← eval t γ ⁏
          ren-val ρ <$> (w ← eval u γ ⁏
                         β-reduce v w)
    ≈⟨ v ⇚ eval t γ ⁏
       ⮦ eval u γ ⟩
          v ← eval t γ ⁏
          w ← eval u γ ⁏
          ren-val ρ <$> β-reduce v w
    ≈⟨ v ⇚ eval t γ ⁏
       w ⇚ eval u γ ⁏
       ren-β-reduce ρ v w ⟩
          v ← eval t γ ⁏
          w ← eval u γ ⁏
          β-reduce (ren-val ρ v) (ren-val ρ w)
    ≈⟨ v ⇚ eval t γ ⁏
       ⮥ eval u γ ⟩
          v  ← eval t γ ⁏
          w′ ← ren-val ρ <$> eval u γ ⁏
          β-reduce (ren-val ρ v) w′
    ≈⟨ v ⇚ eval t γ ⁏
       ∵ ren-eval ρ u γ ⟩
          v  ← eval t γ ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          β-reduce (ren-val ρ v) w′
    ≈⟨ ⮥ eval t γ ⟩
          v′ ← ren-val ρ <$> eval t γ ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          β-reduce v′ w′
    ≈⟨ ∵ ren-eval ρ t γ ⟩
          v′ ← eval t (ren-env ρ γ) ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          β-reduce v′ w′
    ∎
    where open ≈-Reasoning
  ren-eval ρ unit       γ = ≈now unit
  ren-eval ρ (pair t u) γ =
    proof
          ren-val ρ <$> (v ← eval t γ ⁏
                         w ← eval u γ ⁏
                         now (pair v w))
    ≈⟨ ⮦ eval t γ ⟩
          v ← eval t γ ⁏
          ren-val ρ <$> (w ← eval u γ ⁏
                         now (pair v w))
    ≈⟨ v ⇚ eval t γ ⁏
       ⮦ eval u γ ⟩
          v ← eval t γ ⁏
          w ← eval u γ ⁏
          ren-val ρ <$> now (pair v w)
    ≈⟨ v ⇚ eval t γ ⁏
       w ⇚ eval u γ ⁏
       ≈now (pair (ren-val ρ v) (ren-val ρ w)) ⟩
          v ← eval t γ ⁏
          w ← eval u γ ⁏
          now (pair (ren-val ρ v) (ren-val ρ w))
    ≈⟨ v ⇚ eval t γ ⁏
       ⮥ eval u γ ⟩
          v  ← eval t γ ⁏
          w′ ← ren-val ρ <$> eval u γ ⁏
          now (pair (ren-val ρ v) w′)
    ≈⟨ v ⇚ eval t γ ⁏
       ∵ ren-eval ρ u γ ⟩
          v  ← eval t γ ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          now (pair (ren-val ρ v) w′)
    ≈⟨ ⮥ eval t γ ⟩
          v′ ← ren-val ρ <$> eval t γ ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          now (pair v′ w′)
    ≈⟨ ∵ ren-eval ρ t γ ⟩
          v′ ← eval t (ren-env ρ γ) ⁏
          w′ ← eval u (ren-env ρ γ) ⁏
          now (pair v′ w′)
    ∎
    where open ≈-Reasoning
  ren-eval ρ (fst t) γ =
    proof
          ren-val ρ <$> (v ← eval t γ ⁏
                         π₁-reduce v)
    ≈⟨ ⮦ eval t γ ⟩
          v ← eval t γ ⁏
          ren-val ρ <$> π₁-reduce v
    ≈⟨ v ⇚ eval t γ ⁏
       ren-π₁-reduce ρ v ⟩
          v ← eval t γ ⁏
          π₁-reduce (ren-val ρ v)
    ≈⟨ ⮥ eval t γ ⟩
          v′ ← ren-val ρ <$> eval t γ ⁏
          π₁-reduce v′
    ≈⟨ ∵ ren-eval ρ t γ ⟩
          v′ ← eval t (ren-env ρ γ) ⁏
          π₁-reduce v′
    ∎
    where open ≈-Reasoning
  ren-eval ρ (snd t) γ =
    proof
          ren-val ρ <$> (v ← eval t γ ⁏
                         π₂-reduce v)
    ≈⟨ ⮦ eval t γ ⟩
          v ← eval t γ ⁏
          ren-val ρ <$> π₂-reduce v
    ≈⟨ v ⇚ eval t γ ⁏
       ren-π₂-reduce ρ v ⟩
          v ← eval t γ ⁏
          π₂-reduce (ren-val ρ v)
    ≈⟨ ⮥ eval t γ ⟩
          v′ ← ren-val ρ <$> eval t γ ⁏
          π₂-reduce v′
    ≈⟨ ∵ ren-eval ρ t γ ⟩
          v′ ← eval t (ren-env ρ γ) ⁏
          π₂-reduce v′
    ∎
    where open ≈-Reasoning


  ren-∞eval : ∀ {i Γ Δ Δ′ a b} (ρ : Δ′ ≥ Δ) →
              (t : Tm (Γ , a) b) → (γ : Env Δ Γ) (v : Val Δ a) →
              ren-val ρ ∞<$> ∞eval t γ v ∞≈⟨ i ⟩≈ ∞eval t (ren-env ρ γ) (ren-val ρ v)
  ≈force (ren-∞eval ρ t γ v) = ren-eval ρ t (γ , v)


  ren-β-reduce : ∀ {i Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ⇒ b)) (w : Val Δ a) →
                 ren-val ρ <$> β-reduce v w ≈⟨ i ⟩≈ β-reduce (ren-val ρ v) (ren-val ρ w)
  ren-β-reduce ρ (ne v)    w = ≈refl
  ren-β-reduce ρ (lam t γ) w = ≈later (ren-∞eval ρ t γ w)


  ren-π₁-reduce : ∀ {i Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ∧ b)) →
                  ren-val ρ <$> π₁-reduce v ≈⟨ i ⟩≈ π₁-reduce (ren-val ρ v)
  ren-π₁-reduce ρ (ne v)     = ≈refl
  ren-π₁-reduce ρ (pair v w) = ≈refl


  ren-π₂-reduce : ∀ {i Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ∧ b)) →
                  ren-val ρ <$> π₂-reduce v ≈⟨ i ⟩≈ π₂-reduce (ren-val ρ v)
  ren-π₂-reduce ρ (ne v)     = ≈refl
  ren-π₂-reduce ρ (pair v w) = ≈refl
