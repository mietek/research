module BasicIS4.Regular.Hilbert.KripkeSoundness where

open import BasicIS4.Regular.Hilbert.Nested public


module Standard where
  open import BasicIS4.KripkeSemantics.Standard

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ′ b → mono⊩ {A} ξ′ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ′ g ξ″ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ′ ξ″) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ″ g) refl≤ a
    in  h b
  eval (box t)          γ = λ ζ → eval t ᴬᵍtt
  eval (cdist {A} {B}) {u} γ {u′} = λ _ □f {v} ξ′ □a {v′} ζ →
    let f′ = □f reflR ξ′
        a′ = □a reflR
        b′ = f′ a′
    in {!!}
  eval cup              γ = λ _ □a ζ ζ′ → □a (transR ζ ζ′)
  eval cdown            γ = λ _ □a → □a reflR
  eval (cpair {A})      γ = λ _ a ξ′ b → ᴬᵍpair (mono⊩ {A} ξ′ a) b
  eval cfst             γ = λ _ a∧b → ᴬᵍfst a∧b
  eval csnd             γ = λ _ a∧b → ᴬᵍsnd a∧b
  eval tt               γ = ᴬᵍtt

{-
Goal: v′ ⊩ B
———————————
b′ : v ⊩ B
a′ : v ⊩ A
f′ : v ⊩ A → v ⊩ B
———————————
□a : {w′ : World} → v R w′ → w′ ⊩ A
□f : {w′ : World} → u′ R w′ → {w′ = w′₁ : World} → w′ ≤ w′₁ → w′₁ ⊩ A → w′₁ ⊩ B
———————————
ζ  : v R v′
ξ′ : u′ ≤ v
γ  : u ⊩⋆ Γ
———————————
v′ : World
v  : World
._ : u ≤ u′
u′ : World
u  : World
Γ  : Cx Ty
B  : Ty
A  : Ty
-}


module Alternative where
  open import BasicIS4.KripkeSemantics.Alternative

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)          γ = lookup i γ
  eval (app t u)        γ = (eval t γ) refl≤ (eval u γ)
  eval ci               γ = λ _ a → a
  eval (ck {A})         γ = λ _ a ξ′ b → mono⊩ {A} ξ′ a
  eval (cs {A} {B} {C}) γ = λ _ f ξ′ g ξ″ a →
    let h = ((mono⊩ {A ▷ B ▷ C} (trans≤ ξ′ ξ″) f) refl≤ a) refl≤
        b = (mono⊩ {A ▷ B} ξ″ g) refl≤ a
    in  h b
  eval (box t)          γ = λ _ ζ → {!!}
  eval cdist            γ = λ _ □f ξ′ □a ξ″ ζ → {!!}
  eval cup              γ = λ _ □a ξ′ ζ ξ″ ζ″ → {!!}
  eval cdown            γ = λ _ □a → □a refl≤ reflR
  eval (cpair {A})      γ = λ _ a ξ′ b → ᴬᵍpair (mono⊩ {A} ξ′ a) b
  eval cfst             γ = λ _ a∧b → ᴬᵍfst a∧b
  eval csnd             γ = λ _ a∧b → ᴬᵍsnd a∧b
  eval tt               γ = ᴬᵍtt
