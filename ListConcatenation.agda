{-# OPTIONS --rewriting #-}

module A201801.ListConcatenation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas


--------------------------------------------------------------------------------


_⧺_ : ∀ {X} → List X → List X
            → List X
Ξ ⧺ ∙       = Ξ
Ξ ⧺ (Ψ , A) = (Ξ ⧺ Ψ) , A


ldrops : ∀ {X} → {Ξ Ξ′ : List X}
               → (Ψ : List X) → Ξ′ ⊇ Ξ
               → Ψ ⧺ Ξ′ ⊇ Ξ
ldrops Ψ done     = bot⊇
ldrops Ψ (drop η) = drop (ldrops Ψ η)
ldrops Ψ (keep η) = keep (ldrops Ψ η)


rdrops : ∀ {X} → {Ξ Ξ′ : List X}
               → (Ψ : List X) → Ξ′ ⊇ Ξ
               → Ξ′ ⧺ Ψ ⊇ Ξ
rdrops ∙       η = η
rdrops (Ψ , A) η = drop (rdrops Ψ η)


lkeeps : ∀ {X} → {Ξ Ξ′ : List X}
               → (Ψ : List X) → Ξ′ ⊇ Ξ
               → Ψ ⧺ Ξ′ ⊇ Ψ ⧺ Ξ
lkeeps Ψ done     = id⊇
lkeeps Ψ (drop η) = drop (lkeeps Ψ η)
lkeeps Ψ (keep η) = keep (lkeeps Ψ η)


rkeeps : ∀ {X} → {Ξ Ξ′ : List X}
               → (Ψ : List X) → Ξ′ ⊇ Ξ
               → Ξ′ ⧺ Ψ ⊇ Ξ ⧺ Ψ
rkeeps ∙       η = η
rkeeps (Ψ , A) η = keep (rkeeps Ψ η)


--------------------------------------------------------------------------------


push∋ : ∀ {X A B} → {Ξ : List X}
                  → (Ψ : List X) → ((Ξ ⧺ Ψ) , A) ∋ B
                  → ((Ξ , A) ⧺ Ψ) ∋ B
push∋ Ψ       zero    = ren∋ (rdrops Ψ id⊇) zero
push∋ ∙       (suc i) = suc i
push∋ (Ψ , C) (suc i) = ren∋ (keep (rkeeps Ψ (drop id⊇))) i


pull∋ : ∀ {X A B} → {Ξ : List X}
                  → (Ψ : List X) → ((Ξ , A) ⧺ Ψ) ∋ B
                  → ((Ξ ⧺ Ψ) , A) ∋ B
pull∋ ∙       i       = i
pull∋ (Ψ , C) zero    = suc zero
pull∋ (Ψ , C) (suc i) = ren∋ (keep (drop id⊇)) (pull∋ Ψ i)


--------------------------------------------------------------------------------


-- TODO: Move to ListConcatenationLemmas

lid⧺ : ∀ {X} → (Ξ : List X)
             → ∙ ⧺ Ξ ≡ Ξ
lid⧺ ∙       = refl
lid⧺ (Ξ , A) = (_, A) & lid⧺ Ξ


assoc⧺ : ∀ {X} → (Ξ Ψ Φ : List X)
               → (Ξ ⧺ Ψ) ⧺ Φ ≡ Ξ ⧺ (Ψ ⧺ Φ)
assoc⧺ Ξ Ψ ∙       = refl
assoc⧺ Ξ Ψ (Φ , A) = (_, A) & assoc⧺ Ξ Ψ Φ


{-# REWRITE lid⧺ #-}
lid-ldrops : ∀ {X} → {Ξ Ξ′ : List X}
                   → (η : Ξ′ ⊇ Ξ)
                   → ldrops ∙ η ≡ η
lid-ldrops done     = refl
lid-ldrops (drop η) = drop & lid-ldrops η
lid-ldrops (keep η) = keep & lid-ldrops η


--------------------------------------------------------------------------------
