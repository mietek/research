{-# OPTIONS --sized-types #-}

module A201605.AbelChapmanExtended2.RenamingLemmas.Normalization2 where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (sym ; cong)

open import A201605.AbelChapmanExtended.Delay
open import A201605.AbelChapmanExtended.StrongBisimilarity

open import A201605.AbelChapmanExtended2.Syntax
open import A201605.AbelChapmanExtended2.OPE
open import A201605.AbelChapmanExtended2.Renaming
open import A201605.AbelChapmanExtended2.Normalization
open import A201605.AbelChapmanExtended2.RenamingLemmas.OPE
open import A201605.AbelChapmanExtended2.RenamingLemmas.Normalization1




mutual
  ren-readback : ∀ {i Δ Δ′} {a : Ty} (η : Δ′ ⊇ Δ) (v : Val Δ a) →
                 ren-nf η <$> readback v ≈⟨ i ⟩≈ readback (ren-val η v)
  ren-readback {a = ⊥}     η (ne v) =
    proof
          ren-nf η <$> (ne <$> readback-ne v)
    ≈⟨ ⋘ readback-ne v ⟩
          (ren-nf η ∘ ne) <$> readback-ne v
    ≡⟨⟩
          (ne ∘ ren-nen η) <$> readback-ne v
    ≈⟨ ⋙ readback-ne v ⟩
          ne <$> (ren-nen η <$> readback-ne v)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          ne <$> readback-ne (ren-nev η v)
    ∎
    where open ≈-Reasoning
  ren-readback {a = a ∨ b} η (ne v) =
    proof
          ren-nf η <$> (ne <$> readback-ne v)
    ≈⟨ ⋘ readback-ne v ⟩
          (ren-nf η ∘ ne) <$> readback-ne v
    ≡⟨⟩
          (ne ∘ ren-nen η) <$> readback-ne v
    ≈⟨ ⋙ readback-ne v ⟩
          ne <$> (ren-nen η <$> readback-ne v)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          ne <$> readback-ne (ren-nev η v)
    ∎
    where open ≈-Reasoning
  ren-readback {a = a ∨ b} η (inl v) =
    proof
          ren-nf η <$> (inl <$> readback v)
    ≈⟨ ⋘ readback v ⟩
          (ren-nf η ∘ inl) <$> readback v
    ≡⟨⟩
          (inl ∘ ren-nf η) <$> readback v
    ≈⟨ ⋙ readback v ⟩
          inl <$> (ren-nf η <$> readback v)
    ≈⟨ ∵ ren-readback η v ⟩
          inl <$> readback (ren-val η v)
    ∎
    where open ≈-Reasoning
  ren-readback {a = a ∨ b} η (inr v) =
    proof
          ren-nf η <$> (inr <$> readback v)
    ≈⟨ ⋘ readback v ⟩
          (ren-nf η ∘ inr) <$> readback v
    ≡⟨⟩
          (inr ∘ ren-nf η) <$> readback v
    ≈⟨ ⋙ readback v ⟩
          inr <$> (ren-nf η <$> readback v)
    ≈⟨ ∵ ren-readback η v ⟩
          inr <$> readback (ren-val η v)
    ∎
    where open ≈-Reasoning
  ren-readback {a = a ⇒ b} η v      = ≈later (ren-∞η-expand η v)
  ren-readback {a = a ∧ b}  η v      = ≈later (ren-∞ψ-expand η v)
  ren-readback {a = ⊤}     η v      = ≈now unit


  ren-readback-ne : ∀ {i Δ Δ′ a} (η : Δ′ ⊇ Δ) (v : Ne Val Δ a) →
                    ren-nen η <$> readback-ne v ≈⟨ i ⟩≈ readback-ne (ren-nev η v)
  ren-readback-ne η (boom v) =
    proof
          ren-nen η <$> (n ← readback-ne v ⁏
                         now (boom n))
    ≈⟨ ⋘ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen η <$> now (boom n)
    ≡⟨⟩
          n ← readback-ne v ⁏
          now (boom (ren-nen η n))
    ≈⟨ ⋙ readback-ne v ⟩
          n′ ← ren-nen η <$> readback-ne v ⁏
          now (boom n′)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          n′ ← readback-ne (ren-nev η v) ⁏
          now (boom n′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne η (case v wl wr) =
    proof
          ren-nen η <$> (n  ← readback-ne v ⁏
                         ml ← readback wl ⁏
                         mr ← readback wr ⁏
                         now (case n ml mr))
    ≈⟨ ⋘ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen η <$> (ml ← readback wl ⁏
                         mr ← readback wr ⁏
                         now (case n ml mr))
    ≈⟨ n ⇚ readback-ne v ⁏
       ⋘ readback wl ⟩
          n  ← readback-ne v ⁏
          ml ← readback wl ⁏
          ren-nen η <$> (mr ← readback wr ⁏
                         now (case n ml mr))
    ≈⟨ n  ⇚ readback-ne v ⁏
       ml ⇚ readback wl ⁏
       ⋘ readback wr ⟩
          n  ← readback-ne v ⁏
          ml ← readback wl ⁏
          mr ← readback wr ⁏
          ren-nen η <$> now (case n ml mr)
    ≈⟨ n  ⇚ readback-ne v ⁏
       ml ⇚ readback wl ⁏
       mr ⇚ readback wr ⁏
       ≈now (case (ren-nen η n) (ren-nf (lift η) ml) (ren-nf (lift η) mr)) ⟩
          n  ← readback-ne v ⁏
          ml ← readback wl ⁏
          mr ← readback wr ⁏
          now (case (ren-nen η n) (ren-nf (lift η) ml) (ren-nf (lift η) mr))
    ≈⟨ n  ⇚ readback-ne v ⁏
       ml ⇚ readback wl ⁏
       ⋙ readback wr ⟩
          n   ← readback-ne v ⁏
          ml  ← readback wl ⁏
          mr′ ← ren-nf (lift η) <$> readback wr ⁏
          now (case (ren-nen η n) (ren-nf (lift η) ml) mr′)
    ≈⟨ n  ⇚ readback-ne v ⁏
       ml ⇚ readback wl ⁏
       ∵ ren-readback (lift η) wr ⟩
          n   ← readback-ne v ⁏
          ml  ← readback wl ⁏
          mr′ ← readback (ren-val (lift η) wr) ⁏
          now (case (ren-nen η n) (ren-nf (lift η) ml) mr′)
    ≈⟨ n ⇚ readback-ne v ⁏
       ⋙ readback wl ⟩
          n   ← readback-ne v ⁏
          ml′ ← ren-nf (lift η) <$> readback wl ⁏
          mr′ ← readback (ren-val (lift η) wr) ⁏
          now (case (ren-nen η n) ml′ mr′)
    ≈⟨ n ⇚ readback-ne v ⁏
       ∵ ren-readback (lift η) wl ⟩
          n   ← readback-ne v ⁏
          ml′ ← readback (ren-val (lift η) wl) ⁏
          mr′ ← readback (ren-val (lift η) wr) ⁏
          now (case (ren-nen η n) ml′ mr′)
    ≈⟨ ⋙ readback-ne v ⟩
          n′  ← ren-nen η <$> readback-ne v ⁏
          ml′ ← readback (ren-val (lift η) wl) ⁏
          mr′ ← readback (ren-val (lift η) wr) ⁏
          now (case n′ ml′ mr′)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          n′  ← readback-ne (ren-nev η v) ⁏
          ml′ ← readback (ren-val (lift η) wl) ⁏
          mr′ ← readback (ren-val (lift η) wr) ⁏
          now (case n′ ml′ mr′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne η (var x)   = ≈now (var (ren-var η x))
  ren-readback-ne η (app v w) =
    proof
          ren-nen η <$> (n ← readback-ne v ⁏
                         m ← readback w ⁏
                         now (app n m))
    ≈⟨ ⋘ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen η <$> (m ← readback w ⁏
                         now (app n m))
    ≈⟨ n ⇚ readback-ne v ⁏
       ⋘ readback w ⟩
          n ← readback-ne v ⁏
          m ← readback w ⁏
          ren-nen η <$> now (app n m)
    ≡⟨⟩
          n ← readback-ne v ⁏
          m ← readback w ⁏
          now (app (ren-nen η n) (ren-nf η m))
    ≈⟨ n ⇚ readback-ne v ⁏
       ⋙ readback w ⟩
          n  ← readback-ne v ⁏
          m′ ← ren-nf η <$> readback w ⁏
          now (app (ren-nen η n) m′)
    ≈⟨ ⋙ readback-ne v ⟩
          n′ ← ren-nen η <$> readback-ne v ⁏
          m′ ← ren-nf η <$> readback w ⁏
          now (app n′ m′)
    ≈⟨ n′ ⇚ ren-nen η <$> readback-ne v ⁏
       ∵ ren-readback η w ⟩
          n′ ← ren-nen η <$> readback-ne v ⁏
          m′ ← readback (ren-val η w) ⁏
          now (app n′ m′)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          n′ ← readback-ne (ren-nev η v) ⁏
          m′ ← readback (ren-val η w) ⁏
          now (app n′ m′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne η (fst v) =
    proof
          ren-nen η <$> (n ← readback-ne v ⁏
                         now (fst n))
    ≈⟨ ⋘ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen η <$> now (fst n)
    ≡⟨⟩
          n ← readback-ne v ⁏
          now (fst (ren-nen η n))
    ≈⟨ ⋙ readback-ne v ⟩
          n′ ← ren-nen η <$> readback-ne v ⁏
          now (fst n′)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          n′ ← readback-ne (ren-nev η v) ⁏
          now (fst n′)
    ∎
    where open ≈-Reasoning
  ren-readback-ne η (snd v) =
    proof
          ren-nen η <$> (n ← readback-ne v ⁏
                         now (snd n))
    ≈⟨ ⋘ readback-ne v ⟩
          n ← readback-ne v ⁏
          ren-nen η <$> now (snd n)
    ≡⟨⟩
          n ← readback-ne v ⁏
          now (snd (ren-nen η n))
    ≈⟨ ⋙ readback-ne v ⟩
          n′ ← ren-nen η <$> readback-ne v ⁏
          now (snd n′)
    ≈⟨ ∵ ren-readback-ne η v ⟩
          n′ ← readback-ne (ren-nev η v) ⁏
          now (snd n′)
    ∎
    where open ≈-Reasoning


  ren-∞η-expand : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ⇒ b)) →
                  ren-nf η ∞<$> ∞η-expand v ∞≈⟨ i ⟩≈ ∞η-expand (ren-val η v)
  ≈force (ren-∞η-expand η v) =
    proof
          ren-nf η <$> (v′ ← β-reduce (wk-val v) nev₀ ⁏
                        n′ ← readback v′ ⁏
                        now (lam n′))
    ≈⟨ ⋘ β-reduce (wk-val v) nev₀ ⟩
          v′ ← β-reduce (wk-val v) nev₀ ⁏
          ren-nf η <$> (n′ ← readback v′ ⁏
                        now (lam n′))
    ≈⟨ v′ ⇚ β-reduce (wk-val v) nev₀ ⁏
       ⋘ readback v′ ⟩
          v′ ← β-reduce (wk-val v) nev₀ ⁏
          n′ ← readback v′ ⁏
          ren-nf η <$> now (lam n′)
    ≈⟨ v′ ⇚ β-reduce (wk-val v) nev₀ ⁏
       n′ ⇚ readback v′ ⁏
       ≈now (lam (ren-nf (lift η) n′)) ⟩
          v′ ← β-reduce (wk-val v) nev₀ ⁏
          n′ ← readback v′ ⁏
          n″ ← now (ren-nf (lift η) n′) ⁏
          now (lam n″)
    ≈⟨ v′ ⇚ β-reduce (wk-val v) nev₀ ⁏
       ⋙ readback v′ ⟩
          v′ ← β-reduce (wk-val v) nev₀ ⁏
          n″ ← ren-nf (lift η) <$> readback v′ ⁏
          now (lam n″)
    ≈⟨ v′ ⇚ β-reduce (wk-val v) nev₀ ⁏
       ∵ ren-readback (lift η) v′ ⟩
          v′ ← β-reduce (wk-val v) nev₀ ⁏
          n″ ← readback (ren-val (lift η) v′) ⁏
          now (lam n″)
    ≈⟨ ⋙ β-reduce (wk-val v) nev₀ ⟩
          v″ ← ren-val (lift η) <$> β-reduce (wk-val v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≈⟨ ∵ ren-β-reduce (lift η) (wk-val v) nev₀ ⟩
          v″ ← β-reduce (ren-val (lift η) (wk-val v)) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ v → (v′ ← β-reduce v nev₀ ⁏
                     n′ ← readback v′ ⁏
                     now (lam n′)))
            (ren-val-• (lift η) wk v) ⟩
          v″ ← β-reduce (ren-val (weak (η • id)) v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ η′ → (v′ ← β-reduce (ren-val (weak η′) v) nev₀ ⁏
                      n′ ← readback v′ ⁏
                      now (lam n′)))
            (η•id η) ⟩
          v″ ← β-reduce (ren-val (weak η) v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ η′ → (v′ ← β-reduce (ren-val (weak η′) v) nev₀ ⁏
                      n′ ← readback v′ ⁏
                      now (lam n′)))
            (sym (id•η η)) ⟩
          v″ ← β-reduce (ren-val (weak (id • η)) v) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ≡⟨ cong (λ v → (v′ ← β-reduce v nev₀ ⁏
                     n′ ← readback v′ ⁏
                     now (lam n′)))
            (sym (ren-val-• wk η v)) ⟩
          v″ ← β-reduce (wk-val (ren-val η v)) nev₀ ⁏
          n″ ← readback v″ ⁏
          now (lam n″)
    ∎
    where open ≈-Reasoning


  ren-∞ψ-expand : ∀ {i Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∧ b)) →
                 ren-nf η ∞<$> ∞ψ-expand v ∞≈⟨ i ⟩≈ ∞ψ-expand (ren-val η v)
  ≈force (ren-∞ψ-expand η v) =
    proof
          ren-nf η <$> (v′ ← π₁-reduce v ⁏
                        w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ ⋘ π₁-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          ren-nf η <$> (w′ ← π₂-reduce v ⁏
                        n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       ⋘ π₂-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          ren-nf η <$> (n′ ← readback v′ ⁏
                        m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ⋘ readback v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          ren-nf η <$> (m′ ← readback w′ ⁏
                        now (pair n′ m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       ⋘ readback w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m′ ← readback w′ ⁏
          ren-nf η <$> now (pair n′ m′)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       m′ ⇚ readback w′ ⁏
       ≈now (pair (ren-nf η n′) (ren-nf η m′)) ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m′ ← readback w′ ⁏
          now (pair (ren-nf η n′) (ren-nf η m′))
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n′ ⇚ readback v′ ⁏
       ⋙ readback w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n′ ← readback v′ ⁏
          m″ ← ren-nf η <$> readback w′ ⁏
          now (pair (ren-nf η n′) m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ⋙ readback v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← ren-nf η <$>  readback v′ ⁏
          m″ ← ren-nf η <$>  readback w′ ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       n″ ⇚ ren-nf η <$> readback v′ ⁏
       ∵ ren-readback η w′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← ren-nf η <$> readback v′ ⁏
          m″ ← readback (ren-val η w′) ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ π₁-reduce v ⁏
       w′ ⇚ π₂-reduce v ⁏
       ∵ ren-readback η v′ ⟩
          v′ ← π₁-reduce v ⁏
          w′ ← π₂-reduce v ⁏
          n″ ← readback (ren-val η v′) ⁏
          m″ ← readback (ren-val η w′) ⁏
          now (pair n″ m″)
    ≈⟨ v′ ⇚ (π₁-reduce v) ⁏
       ⋙ π₂-reduce v ⟩
          v′ ← π₁-reduce v ⁏
          w″ ← ren-val η <$> π₂-reduce v ⁏
          n″ ← readback (ren-val η v′) ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ ⋙ π₁-reduce v ⟩
          v″ ← ren-val η <$> π₁-reduce v ⁏
          w″ ← ren-val η <$> π₂-reduce v ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ v″ ⇚ ren-val η <$> π₁-reduce v ⁏
       ∵ ren-π₂-reduce η v ⟩
          v″ ← ren-val η <$> π₁-reduce v ⁏
          w″ ← π₂-reduce (ren-val η v) ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ≈⟨ ∵ ren-π₁-reduce η v ⟩
          v″ ← π₁-reduce (ren-val η v) ⁏
          w″ ← π₂-reduce (ren-val η v) ⁏
          n″ ← readback v″ ⁏
          m″ ← readback w″ ⁏
          now (pair n″ m″)
    ∎
    where open ≈-Reasoning
