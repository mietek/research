module StdLPTTLemmas where

open import Prelude
open import Fin
open import FinLemmas
open import Vec
open import StdS4TTTerms
open import StdS4TTTermsLemmas
open import StdLPTT


--------------------------------------------------------------------------------


{-
    box : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
                       {A : Prop d}
                    → Δ ⋙ [ ∙ ⊢ M ⦂ A true ]
                    → Δ ⋙ [ Γ ⊢ BOX M ⦂ [ M ] A true ]

    letbox : ∀ {d g M N O} → {Δ : Validities d} {Γ : Truths d g}
                              {A : Prop d} {B : Prop (suc d)}
                              {Γ° : Truths (suc d) g} {{_ : Γ° ≡ MWKSₜ Γ}}
                              {B° : Prop d} {{_ : B° ≡ MCUTₚ O B}}
                           → Δ ⋙ [ Γ ⊢ M ⦂ [ O ] A true ] → Δ , A valid ⋙ [ Γ° ⊢ N ⦂ B true ]
                           → Δ ⋙ [ Γ ⊢ LETBOX M N ⦂ B° true ]
-}



id-MSUBₚ : ∀ {d} → (A : Prop d)
                 → MSUBₚ MIDS₁ A ≡ A
id-MSUBₚ BASE      = refl
id-MSUBₚ (A ⊃ B)   = _⊃_ & id-MSUBₚ A ⊗ id-MSUBₚ B
id-MSUBₚ ([ M ] A) = [_]_ & id-MSUB M ⊗ id-MSUBₚ A


expand-MSUBₚ : ∀ {d n} → (x : Terms₁ d n) (M : Term₁ d) (A : Prop n)
                       → MSUBₚ (x , M) (MWKₚ A) ≡ MSUBₚ x A
expand-MSUBₚ x M BASE      = refl
expand-MSUBₚ x M (A ⊃ B)   = _⊃_ & expand-MSUBₚ x M A ⊗ expand-MSUBₚ x M B
expand-MSUBₚ x M ([ N ] A) = [_]_ & expand-MSUB x M N ⊗ expand-MSUBₚ x M A


unbox : ∀ {d g M N} → {Δ : Validities d} {Γ : Truths d g}
                       {A : Prop d}
                    → Δ ⋙ [ Γ ⊢ M ⦂ [ N ] A true ]
                    → Δ ⋙ [ Γ ⊢ LETBOX M MVZ ⦂ A true ]
unbox {N = N} {A = A} 𝒟 = letbox {{refl}} {{lem}} 𝒟 mvz
  where
    lem : A ≡ MCUTₚ N (MWKₚ A)
    lem = id-MSUBₚ A ⁻¹ ⋮ expand-MSUBₚ MIDS₁ N A ⁻¹


ex1 : ∀ {d g} → {Δ : Validities (suc d)} {Γ : Truths (suc d) g}
                 {A : Prop (suc d)}
              → Δ ⋙ [ Γ ⊢ BOX (LAM (LETBOX VZ (BOX MVZ)))
                               ⦂ [ LAM (LETBOX VZ (BOX MVZ)) ] ([ MVZ ] A ⊃ A) true ]
ex1 {A = A} = box (lam (letbox {{refl}} {{lem}} vz (box mvz)))
  where
    lem : A ≡ MCUTₚ MVZ ([ MVZ ] MWKₚ A)
    lem = {!!}


--------------------------------------------------------------------------------
