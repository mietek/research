module AbelChapmanExtended.RenamingLemmas.Normalization1 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.RenamingLemmas.OPE
open import AbelChapmanExtended.StrongBisimilarity
open import AbelChapmanExtended.Syntax




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
  ren-eval η (boom t) ρ =
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
  ren-eval η (inl t) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         now (inl v))
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> now (inl v)
    ≈⟨ v ⇚ eval t ρ ⁏
       ≈now (inl (ren-val η v)) ⟩
          v ← eval t ρ ⁏
          now (inl (ren-val η v))
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          now (inl v′)
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          now (inl v′)
    ∎
    where open ≈-Reasoning
  ren-eval η (inr t) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         now (inr v))
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> now (inr v)
    ≈⟨ v ⇚ eval t ρ ⁏
       ≈now (inr (ren-val η v)) ⟩
          v ← eval t ρ ⁏
          now (inr (ren-val η v))
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          now (inr v′)
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          now (inr v′)
    ∎
    where open ≈-Reasoning
  ren-eval η (case t ul ur) ρ =
    proof
          ren-val η <$> (v ← eval t ρ ⁏
                         κ-reduce v ul ur ρ)
    ≈⟨ ⋘ eval t ρ ⟩
          v ← eval t ρ ⁏
          ren-val η <$> κ-reduce v ul ur ρ
    ≈⟨ v ⇚ eval t ρ ⁏
       ren-κ-reduce η v ul ur ρ ⟩
          v ← eval t ρ ⁏
          κ-reduce (ren-val η v) ul ur (ren-env η ρ)
    ≈⟨ ⋙ eval t ρ ⟩
          v′ ← ren-val η <$> eval t ρ ⁏
          κ-reduce v′ ul ur (ren-env η ρ)
    ≈⟨ ∵ ren-eval η t ρ ⟩
          v′ ← eval t (ren-env η ρ) ⁏
          κ-reduce v′ ul ur (ren-env η ρ)
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


  ren-κ-reduce : ∀ {i Γ Δ′ Δ a b c} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∨ b))
                 (ul : Tm (Γ , a) c) (ur : Tm (Γ , b) c) (ρ : Env Δ Γ) →
                 ren-val η <$> κ-reduce v ul ur ρ ≈⟨ i ⟩≈
                 κ-reduce (ren-val η v) ul ur (ren-env η ρ)
  ren-κ-reduce η (ne v)  ul ur ρ =
    proof
          ren-val η <$> (wl ← eval ul (wk-env ρ , nev₀) ⁏
                         wr ← eval ur (wk-env ρ , nev₀) ⁏
                         now (ne (case v wl wr)))
    ≈⟨ ⋘ eval ul (wk-env ρ , nev₀) ⟩
          wl ← eval ul (wk-env ρ , nev₀) ⁏
          ren-val η <$> (wr ← eval ur (wk-env ρ , nev₀) ⁏
                         now (ne (case v wl wr)))
    ≈⟨ wl ⇚ eval ul (wk-env ρ , nev₀) ⁏
       ⋘ eval ur (wk-env ρ , nev₀) ⟩
          wl ← eval ul (wk-env ρ , nev₀) ⁏
          wr ← eval ur (wk-env ρ , nev₀) ⁏
          ren-val η <$> now (ne (case v wl wr))
    ≈⟨ wl ⇚ eval ul (wk-env ρ , nev₀) ⁏
       wr ⇚ eval ur (wk-env ρ , nev₀) ⁏
       ≈now (ne (ren-nev η (case v wl wr))) ⟩
          wl ← eval ul (wk-env ρ , nev₀) ⁏
          wr ← eval ur (wk-env ρ , nev₀) ⁏
          now (ne (ren-nev η (case v wl wr)))
    ≡⟨⟩
          wl ← eval ul (wk-env ρ , nev₀) ⁏
          wr ← eval ur (wk-env ρ , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) (ren-val (lift η) wr)))
    ≈⟨ wl ⇚ eval ul (wk-env ρ , nev₀) ⁏
       ⋙ eval ur (wk-env ρ , nev₀) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← ren-val (lift η) <$> eval ur (wk-env ρ , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≈⟨ wl ⇚ eval ul (wk-env ρ , nev₀) ⁏
       ∵ ren-eval (lift η) ur (wk-env ρ , nev₀) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (ren-env (lift η) (wk-env ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≡⟨ cong (λ ρ′ → (wl  ← eval ul (wk-env ρ , nev₀) ⁏
                      wr′ ← eval ur (ρ′ , nev₀) ⁏
                      now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))))
            (ren-env-• (lift η) wk ρ) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (ren-env (weak (η • id)) ρ , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≡⟨ cong (λ η′ → (wl  ← eval ul (wk-env ρ , nev₀) ⁏
                      wr′ ← eval ur (ren-env (weak η′) ρ , nev₀) ⁏
                      now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))))
            (η•id η) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (ren-env (weak η) ρ , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≡⟨ cong (λ η′ → (wl  ← eval ul (wk-env ρ , nev₀) ⁏
                      wr′ ← eval ur (ren-env (weak η′) ρ , nev₀) ⁏
                      now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))))
            (sym (id•η η)) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (ren-env (weak (id • η)) ρ , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≡⟨ cong (λ ρ′ → (wl  ← eval ul (wk-env ρ , nev₀) ⁏
                      wr′ ← eval ur (ρ′ , nev₀) ⁏
                      now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))))
            (sym (ren-env-• wk η ρ)) ⟩
          wl  ← eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) (ren-val (lift η) wl) wr′))
    ≈⟨ ⋙ eval ul (wk-env ρ , nev₀) ⟩
          wl′ ← ren-val (lift η) <$> eval ul (wk-env ρ , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ≈⟨ ∵ ren-eval (lift η) ul (wk-env ρ , nev₀) ⟩
          wl′ ← eval ul (ren-env (lift η) (wk-env ρ) , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ≡⟨ cong (λ ρ′ → (wl′ ← eval ul (ρ′ , nev₀) ⁏
                      wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
                      now (ne (case (ren-nev η v) wl′ wr′))))
            (ren-env-• (lift η) wk ρ) ⟩
          wl′ ← eval ul (ren-env (weak (η • id)) ρ , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ≡⟨ cong (λ η′ → (wl′ ← eval ul (ren-env (weak η′) ρ , nev₀) ⁏
                      wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
                      now (ne (case (ren-nev η v) wl′ wr′))))
            (η•id η) ⟩
          wl′ ← eval ul (ren-env (weak η) ρ , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ≡⟨ cong (λ η′ → (wl′ ← eval ul (ren-env (weak η′) ρ , nev₀) ⁏
                      wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
                      now (ne (case (ren-nev η v) wl′ wr′))))
            (sym (id•η η)) ⟩
          wl′ ← eval ul (ren-env (weak (id • η)) ρ , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ≡⟨ cong (λ ρ′ → (wl′ ← eval ul (ρ′ , nev₀) ⁏
                      wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
                      now (ne (case (ren-nev η v) wl′ wr′))))
            (sym (ren-env-• wk η ρ)) ⟩
          wl′ ← eval ul (wk-env (ren-env η ρ) , nev₀) ⁏
          wr′ ← eval ur (wk-env (ren-env η ρ) , nev₀) ⁏
          now (ne (case (ren-nev η v) wl′ wr′))
    ∎
    where open ≈-Reasoning
  ren-κ-reduce η (inl v) ul ur ρ = ≈later (ren-∞eval η ul (ρ , v))
  ren-κ-reduce η (inr v) ul ur ρ = ≈later (ren-∞eval η ur (ρ , v))


  ren-β-reduce : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ⇒ b)) (w : Val Δ a) →
                 ren-val η <$> β-reduce v w ≈⟨ i ⟩≈ β-reduce (ren-val η v) (ren-val η w)
  ren-β-reduce η (ne v)    w = ≈refl
  ren-β-reduce η (lam t ρ) w = ≈later (ren-∞eval η t (ρ , w))
