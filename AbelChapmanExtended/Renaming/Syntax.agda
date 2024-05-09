module AbelChapmanExtended.Renaming.Syntax where

open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.OPE




Ren : ∀ {X : Set} → (Cx → X → Set) → Cx → Cx → Set
Ren Ξ Γ Γ′ = ∀ {x} → Ξ Γ x → Ξ Γ′ x


mutual
  ren-var : ∀ {Γ Γ′} → Γ′ ⊇ Γ → Ren Var Γ Γ′
  ren-var id       x       = x
  ren-var (weak η) x       = pop (ren-var η x)
  ren-var (lift η) top     = top
  ren-var (lift η) (pop x) = pop (ren-var η x)

  ren-nen : ∀ {Δ Δ′} → Δ′ ⊇ Δ → Ren (Ne Nf) Δ Δ′
  ren-nen η (loop n)  = loop (ren-nen η n)
  ren-nen η (var x)   = var (ren-var η x)
  ren-nen η (app n m) = app (ren-nen η n) (ren-nf η m)
  ren-nen η (fst n)   = fst (ren-nen η n)
  ren-nen η (snd n)   = snd (ren-nen η n)

  ren-nev : ∀ {Δ Δ′} → Δ′ ⊇ Δ → Ren (Ne Val) Δ Δ′
  ren-nev η (loop v)  = loop (ren-nev η v)
  ren-nev η (var x)   = var (ren-var η x)
  ren-nev η (app v w) = app (ren-nev η v) (ren-val η w)
  ren-nev η (fst v)   = fst (ren-nev η v)
  ren-nev η (snd v)   = snd (ren-nev η v)

  ren-nf : ∀ {Δ Δ′} → Δ′ ⊇ Δ → Ren Nf Δ Δ′
  ren-nf η (ne n)     = ne (ren-nen η n)
  ren-nf η (lam n)    = lam (ren-nf (lift η) n)
  ren-nf η (pair n m) = pair (ren-nf η n) (ren-nf η m)
  ren-nf η unit       = unit

  ren-val : ∀ {Δ Δ′} → Δ′ ⊇ Δ → Ren Val Δ Δ′
  ren-val η (ne n)     = ne (ren-nev η n)
  ren-val η (lam t ρ)  = lam t (ren-env η ρ)
  ren-val η (pair v w) = pair (ren-val η v) (ren-val η w)
  ren-val η unit       = unit

  ren-env : ∀ {Δ Δ′} → Δ′ ⊇ Δ → Ren Env Δ Δ′
  ren-env η ∅       = ∅
  ren-env η (ρ , v) = ren-env η ρ , ren-val η v


wk : ∀ {Γ a} → (Γ , a) ⊇ Γ
wk = weak id

wk-val : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
wk-val = ren-val wk
