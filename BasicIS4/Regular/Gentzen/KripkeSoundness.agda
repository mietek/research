module BasicIS4.Regular.Gentzen.KripkeSoundness where

open import BasicIS4.Regular.Gentzen public


module Standard where
  open import BasicIS4.KripkeSemantics.Standard

  -- NOTE: We seem to require mmono⊩ which is almost certainly false.
  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval {□ A} (multibox ts u) γ = λ ζ →
      let δ  = eval⋆ ts γ
          v′ = eval u δ
      in mmono⊩ {A} ζ v′
--    -- NOTE: Cutting this fails the termination check.
--    let v  = multicut⊢ ts u
--        v′ = eval v γ
--    in mmono⊩ {A} ζ v′
    eval (down t)        γ = (eval t γ) reflR
    eval (pair t u)      γ = ᴬᵍpair (eval t γ) (eval u γ)
    eval (fst t)         γ = ᴬᵍfst (eval t γ)
    eval (snd t)         γ = ᴬᵍsnd (eval t γ)
    eval tt              γ = ᴬᵍtt

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ᴬᵍtt          γ = ᴬᵍtt
    eval⋆ {Π , A} (ᴬᵍpair ts t) γ = ᴬᵍpair (eval⋆ ts γ) (eval t γ)

{-
Goal: w′ ⊩ A
————————————
v′ : w ⊩ A
δ  : w ⊩⋆ (□⋆ Π)
————————————
-- v′ : w ⊩ A
-- v  : Γ ⊢ A
————————————
ζ  : w R w′
γ  : w ⊩⋆ Γ
u  : (□⋆ Π) ⊢ A
ts : Γ ⊢⋆ (□⋆ Π)
————————————
w′ : World
w  : World
Π  : Cx Ty
Γ  : Cx Ty
A  : Ty
-}


module Alternative where
  open import BasicIS4.KripkeSemantics.Alternative

  -- NOTE: We seem to require mmono⊩ which is almost certainly false.
  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
    eval (var i)         γ = lookup i γ
    eval (lam t)         γ = λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a)
    eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
    eval {□ A} (multibox ts u) γ = λ ξ ζ →
      let δ  = eval⋆ ts γ
          v′ = eval u δ
          v″ = mono⊩ {A} ξ v′
      in mmono⊩ {A} ζ v″
--    -- NOTE: Cutting this fails the termination check.
--    let v  = multicut⊢ ts u
--        v′ = eval v γ
--        v″ = mono⊩ {A} ξ v′
--    in mmono⊩ {A} ζ v″
    eval (down t)        γ = (eval t γ) refl≤ reflR
    eval (pair t u)      γ = ᴬᵍpair (eval t γ) (eval u γ)
    eval (fst t)         γ = ᴬᵍfst (eval t γ)
    eval (snd t)         γ = ᴬᵍsnd (eval t γ)
    eval tt              γ = ᴬᵍtt

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
    eval⋆ {⌀}     ᴬᵍtt          γ = ᴬᵍtt
    eval⋆ {Π , A} (ᴬᵍpair ts t) γ = ᴬᵍpair (eval⋆ ts γ) (eval t γ)

{-
Goal: w″ ⊩ A
—————————————
v″ : w′ ⊩ A
v′ : w ⊩ A
δ  : w ⊩⋆ (□⋆ Π)
—————————————
-- v″ : w′ ⊩ A
-- v′ : w ⊩ A
-- v  : Γ ⊢ A
—————————————
ζ  : w′ R w″
ξ  : w ≤ w′
γ  : w ⊩⋆ Γ
u  : (□⋆ Π) ⊢ A
ts : Γ ⊢⋆ (□⋆ Π)
—————————————
w″ : World
w′ : World
w  : World
Π  : Cx Ty
Γ  : Cx Ty
A  : Ty
-}
