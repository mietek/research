module AbelChapmanExtended.Termination.Readback where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (sym ; cong)

open import AbelChapmanExtended.Delay
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.StrongBisimilarity
open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.Termination.Eval




mutual
  ren-readback : ∀ {i Δ Δ′} {a : Ty} (ρ : Δ′ ≥ Δ) (v : Val Δ a) →
                 ren-nf ρ <$> readback v ≈⟨ i ⟩≈ readback (ren-val ρ v)
  ren-readback {a = ★}      ρ (ne v) =
    proof
          ren-nf ρ <$> (ne <$> readback-ne v)
    ≈⟨ ⮦ readback-ne v ⟩
          (ren-nf ρ ∘ ne) <$> readback-ne v
    ≡⟨⟩
          (ne ∘ ren-nen ρ) <$> readback-ne v
    ≈⟨ ⮥ readback-ne v ⟩
          ne <$> (ren-nen ρ <$> readback-ne v)
    ≈⟨ ∵ ren-readback-ne ρ v ⟩
          ne <$> readback-ne (ren-nev ρ v)
    ∎
    where open ≈-Reasoning
  ren-readback {a = a ⇒ b} ρ v      = ≈later (ren-∞η-expand ρ v)
  ren-readback {a = ⊤}     ρ v      = ≈now unit
  ren-readback {a = a ∧ b}  ρ v      = ≈later (ren-∞π-expand ρ v)


  ren-readback-ne : ∀ {i Δ Δ′ a} (ρ : Δ′ ≥ Δ) (v : Ne Val Δ a) →
                    ren-nen ρ <$> readback-ne v ≈⟨ i ⟩≈ readback-ne (ren-nev ρ v)
  ren-readback-ne ρ (var x)   = ≈now (var (ren-var ρ x))
  ren-readback-ne ρ (app v w) =
    proof
          ren-nen ρ <$> (n ← readback-ne v ⁏
                         m ← readback w ⁏
                         now (app n m))
    ≈⟨ ⮦ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen ρ <$> (m ← readback w ⁏
                         now (app n m))
    ≈⟨ n ⇚ readback-ne v ⁏
       ⮦ readback w ⟩
          n ← readback-ne v ⁏
          m ← readback w ⁏
          ren-nen ρ <$> now (app n m)
    ≡⟨⟩
          n ← readback-ne v ⁏
          m ← readback w ⁏
          now (app (ren-nen ρ n) (ren-nf ρ m))
    ≈⟨ n ⇚ readback-ne v ⁏
       ⮥ readback w ⟩
          n  ← readback-ne v ⁏
          m′ ← ren-nf ρ <$> readback w ⁏
          now (app (ren-nen ρ n) m′)
    ≈⟨ ⮥ readback-ne v ⟩
          n′ ← ren-nen ρ <$> readback-ne v ⁏
          m′ ← ren-nf ρ <$> readback w ⁏
          now (app n′ m′)
    ≈⟨ n′ ⇚ ren-nen ρ <$> readback-ne v ⁏
       ∵ ren-readback ρ w ⟩
          n′ ← ren-nen ρ <$> readback-ne v ⁏
          m′ ← readback (ren-val ρ w) ⁏
          now (app n′ m′)
    ≈⟨ ∵ ren-readback-ne ρ v ⟩
          n′ ← readback-ne (ren-nev ρ v) ⁏
          m′ ← readback (ren-val ρ w) ⁏
          now (app n′ m′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne ρ (fst v) =
    proof
          ren-nen ρ <$> (n ← readback-ne v ⁏
                         now (fst n))
    ≈⟨ ⮦ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen ρ <$> now (fst n)
    ≡⟨⟩
          n ← readback-ne v ⁏
          now (fst (ren-nen ρ n))
    ≈⟨ ⮥ readback-ne v ⟩
          n′ ← ren-nen ρ <$> readback-ne v ⁏
          now (fst n′)
    ≈⟨ ∵ ren-readback-ne ρ v ⟩
          n′ ← readback-ne (ren-nev ρ v) ⁏
          now (fst n′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne ρ (snd v) =
    proof
          ren-nen ρ <$> (n ← readback-ne v ⁏
                         now (snd n))
    ≈⟨ ⮦ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen ρ <$> now (snd n)
    ≡⟨⟩
          n ← readback-ne v ⁏
          now (snd (ren-nen ρ n))
    ≈⟨ ⮥ readback-ne v ⟩
          n′ ← ren-nen ρ <$> readback-ne v ⁏
          now (snd n′)
    ≈⟨ ∵ ren-readback-ne ρ v ⟩
          n′ ← readback-ne (ren-nev ρ v) ⁏
          now (snd n′)
    ∎
    where open ≈-Reasoning


  ren-∞η-expand : ∀ {i Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ⇒ b)) →
                  ren-nf ρ ∞<$> ∞η-expand v ∞≈⟨ i ⟩≈ ∞η-expand (ren-val ρ v)
  ≈force (ren-∞η-expand ρ v) =
    proof
          ren-nf ρ <$> (v′ ← β-reduce (vk v) (ne (var top)) ⁏
                        n′ ← readback v′ ⁏
                        now (lam n′))
    ≈⟨ ⮦ β-reduce (vk v) (ne (var top)) ⟩
          v′ ← β-reduce (vk v) nev₀ ⁏
          ren-nf ρ <$> (n′ ← readback v′ ⁏
                        now (lam n′))
    ≈⟨ v′ ⇚ β-reduce (vk v) nev₀ ⁏
       ⮦ readback v′ ⟩
          v′ ← β-reduce (vk v) nev₀ ⁏
          n′ ← readback v′ ⁏
          ren-nf ρ <$> now (lam n′)
    ≈⟨ v′ ⇚ β-reduce (vk v) nev₀ ⁏
       n′ ⇚ readback v′ ⁏
       ≈now (lam (ren-nf (lift ρ) n′)) ⟩
          v′ ← β-reduce (vk v) nev₀ ⁏
          n′ ← readback v′ ⁏
          n″ ← now (ren-nf (lift ρ) n′) ⁏
          now (lam n″)
    ≈⟨ v′ ⇚ β-reduce (vk v) nev₀ ⁏
       ⮥ readback v′ ⟩
          v′ ← β-reduce (vk v) nev₀ ⁏
          n″ ← ren-nf (lift ρ) <$> readback v′ ⁏
          now (lam n″)
    ≈⟨ v′ ⇚ β-reduce (vk v) nev₀ ⁏
       ∵ ren-readback (lift ρ) v′ ⟩
          v′ ← β-reduce (vk v) nev₀ ⁏
          n″ ← readback (ren-val (lift ρ) v′) ⁏
          now (lam n″)
    ≈⟨ ⮥ β-reduce (vk v) nev₀ ⟩
          v″ ← ren-val (lift ρ) <$> β-reduce (vk v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≈⟨ ∵ ren-β-reduce (lift ρ) (vk v) nev₀ ⟩
          v″ ← β-reduce (ren-val (lift ρ) (vk v)) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ v → (v′ ← β-reduce v nev₀ ⁏
                     n′ ← readback v′ ⁏
                     now (lam n′)))
            (ren-val-• (lift ρ) wk v) ⟩
          v″ ← β-reduce (ren-val (weak (ρ • id)) v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ ρ′ → (v′ ← β-reduce (ren-val (weak ρ′) v) nev₀ ⁏
                      n′ ← readback v′ ⁏
                      now (lam n′)))
            (ρ•id ρ) ⟩
          v″ ← β-reduce (ren-val (weak ρ) v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ v → (v′ ← β-reduce v nev₀ ⁏
                     n′ ← readback v′ ⁏
                     now (lam n′)))
            (sym (ren-val-• wk ρ v)) ⟩
          v″ ← β-reduce (vk (ren-val ρ v)) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ∎
    where open ≈-Reasoning


  ren-∞π-expand : ∀ {i Δ Δ′ a b} (ρ : Δ′ ≥ Δ) (v : Val Δ (a ∧ b)) →
                 ren-nf ρ ∞<$> ∞π-expand v ∞≈⟨ i ⟩≈ ∞π-expand (ren-val ρ v)
  ≈force (ren-∞π-expand ρ v) =
    proof
          ren-nf ρ <$> (v′ ← π₁-reduce v ⁏
                        w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ ⮦ π₁-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          ren-nf ρ <$> (w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       ⮦ π₂-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          ren-nf ρ <$> (n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ⮦ readback v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          ren-nf ρ <$> (m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       ⮦ readback w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m′ ← readback w′ ⁏
          ren-nf ρ <$> now (pair n′ m′)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       m′ ⇚ readback w′ ⁏
       ≈now (pair (ren-nf ρ n′) (ren-nf ρ m′)) ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m′ ← readback w′ ⁏
          now (pair (ren-nf ρ n′) (ren-nf ρ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       ⮥ readback w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m″ ← ren-nf ρ <$> readback w′ ⁏
          now (pair (ren-nf ρ n′) m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ⮥ readback v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← ren-nf ρ <$>  readback v′ ⁏
          m″ ← ren-nf ρ <$>  readback w′ ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n″ ⇚ ren-nf ρ <$> readback v′ ⁏
       ∵ ren-readback ρ w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← ren-nf ρ <$> readback v′ ⁏
          m″ ← readback (ren-val ρ w′) ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ∵ ren-readback ρ v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← readback (ren-val ρ v′) ⁏
          m″ ← readback (ren-val ρ w′) ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ (π₁-reduce v) ⁏
       ⮥ π₂-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          w″ ← ren-val ρ <$> π₂-reduce v ⁏
          n″ ← readback (ren-val ρ v′) ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ ⮥ π₁-reduce v ⟩
          v″ ← ren-val ρ <$> π₁-reduce v ⁏
          w″ ← ren-val ρ <$> π₂-reduce v ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ v″ ⇚ ren-val ρ <$> π₁-reduce v ⁏
       ∵ ren-π₂-reduce ρ v ⟩
          v″ ← ren-val ρ <$> π₁-reduce v ⁏
          w″ ← π₂-reduce (ren-val ρ v) ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ ∵ ren-π₁-reduce ρ v ⟩
          v″ ← π₁-reduce (ren-val ρ v) ⁏
          w″ ← π₂-reduce (ren-val ρ v) ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ∎
    where open ≈-Reasoning
