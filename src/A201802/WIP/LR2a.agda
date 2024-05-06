{-# OPTIONS --allow-unsolved-metas #-}

module A201802.WIP.LR2a where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec

open import A201802.WIP.LR1a


--------------------------------------------------------------------------------


data IsVal {g} : Exp g → Set
  where
    instance
      val-lam   : ∀ {M} → IsVal (lam M)
      val-true  : IsVal true
      val-false : IsVal false


record Val (g : Nat) : Set
  where
    constructor val
    field
      term   : Exp g
      {{iv}} : IsVal term


data EvCx (g : Nat) : Set
  where
    ec-[]   : EvCx g
    ec-app₁ : EvCx g → Exp g → EvCx g
    ec-app₂ : Val g → EvCx g → EvCx g
    ec-if   : EvCx g → Exp g → Exp g → EvCx g


_[_] : ∀ {g} → EvCx g → Exp g → Exp g
ec-[]           [ e ]  = e
ec-app₁ E e₂    [ e₁ ] = app (E [ e₁ ]) e₂
ec-app₂ v E     [ e ]  = app (Val.term v) (E [ e ])
ec-if   E e₂ e₃ [ e₁ ] = if (E [ e₁ ]) e₂ e₃


infix 3 _↦_
data _↦_ {g} : Exp g → Exp g → Set
  where
    red-app-lam  : ∀ {e₁ e₂} → app (lam e₁) e₂ ↦ cut e₂ e₁
    red-if-true  : ∀ {e₁ e₂} → if true e₁ e₂ ↦ e₁
    red-if-false : ∀ {e₁ e₂} → if false e₁ e₂ ↦ e₂
    cong-ec      : ∀ {e e′} → (E : EvCx g) → e ↦ e′
                            → E [ e ] ↦ E [ e′ ]


infix 3 _⤅_
data _⤅_ {g} : Exp g → Exp g → Set
  where
    done : ∀ {e} → e ⤅ e
    step : ∀ {e e″ e′} → e ↦ e″ → e″ ⤅ e′ → e ⤅ e′


steps : ∀ {g} → {e e″ e′ : Exp g}
              → e ⤅ e″ → e″ ⤅ e′
              → e ⤅ e′
steps done                e⤅e′  = e⤅e′
steps (step e↦e‴ e‴⤅e″) e″⤅e′ = step e↦e‴ (steps e‴⤅e″ e″⤅e′)


infix 3 _⇓_
_⇓_ : ∀ {g} → Exp g → Val g → Set
e ⇓ v = e ⤅ Val.term v


_⇓ : ∀ {g} → Exp g → Set
e ⇓ = Σ (Val _) (\ v → e ⇓ v)


--------------------------------------------------------------------------------


mutual
  tp↦ : ∀ {g e e′ τ} → {Γ : Types g}
                      → e ↦ e′ → Γ ⊢ e ⦂ τ
                      → Γ ⊢ e′ ⦂ τ
  tp↦ red-app-lam       (APP (LAM D₁) D₂) = CUT D₂ D₁
  tp↦ red-if-true       (IF D₁ D₂ D₃)     = D₂
  tp↦ red-if-false      (IF D₁ D₂ D₃)     = D₃
  tp↦ (cong-ec E e↦e′) D                 = PLUG E e↦e′ D

  PLUG : ∀ {g e e′ τ} → {Γ : Types g}
                      → (E : EvCx g) → e ↦ e′ → Γ ⊢ E [ e ] ⦂ τ
                      → Γ ⊢ E [ e′ ] ⦂ τ
  PLUG ec-[]           e↦e′ D             = tp↦ e↦e′ D
  PLUG (ec-app₁ E e₂)  e↦e′ (APP D₁ D₂)   = APP (PLUG E e↦e′ D₁) D₂
  PLUG (ec-app₂ v E)   e↦e′ (APP D₁ D₂)   = APP D₁ (PLUG E e↦e′ D₂)
  PLUG (ec-if E e₂ e₃) e↦e′ (IF D₁ D₂ D₃) = IF (PLUG E e↦e′ D₁) D₂ D₃


tp⤅ : ∀ {g e e′ τ} → {Γ : Types g}
                    → e ⤅ e′ → Γ ⊢ e ⦂ τ
                    → Γ ⊢ e′ ⦂ τ
tp⤅ done                D = D
tp⤅ (step e↦e″ e″⤅e′) D = tp⤅ (e″⤅e′) (tp↦ e↦e″ D)


--------------------------------------------------------------------------------


lem-if-true : ∀ {g} → {e₁ e₂ e₂′ e₃ : Exp g}
                    → e₁ ⤅ true → e₂ ⤅ e₂′
                    → if e₁ e₂ e₃ ⤅ e₂′
lem-if-true done                     e₂⤅e₂′ = step red-if-true e₂⤅e₂′
lem-if-true (step e₁↦e₁″ e₁″⤅true) e₂⤅e₂′ = step (cong-ec (ec-if ec-[] _ _) e₁↦e₁″) (lem-if-true e₁″⤅true e₂⤅e₂′)


lem-if-false : ∀ {g} → {e₁ e₂ e₃ e₃′ : Exp g}
                     → e₁ ⤅ false → e₃ ⤅ e₃′
                     → if e₁ e₂ e₃ ⤅ e₃′
lem-if-false done                      e₃⤅e₃′ = step red-if-false e₃⤅e₃′
lem-if-false (step e₁↦e₁′ e₁′⤅false) e₃⤅e₃′ = step (cong-ec (ec-if ec-[] _ _) e₁↦e₁′) (lem-if-false e₁′⤅false e₃⤅e₃′)


private
  module Impossible
    where
      sn : ∀ {M A} → ∙ ⊢ M ⦂ A → M ⇓
      sn (VAR ())
      sn (LAM D)       = val (lam _) , done
      sn (APP D₁ D₂)   = {!!}
      sn TRUE          = val true , done
      sn FALSE         = val false , done
      sn (IF D₁ D₂ D₃) with sn D₁ | sn D₂ | sn D₃
      sn (IF D₁ D₂ D₃) | e₁′ , e₁⤅e₁′ | e₂⇓ | e₃⇓ with tp⤅ e₁⤅e₁′ D₁
      sn (IF D₁ D₂ D₃) | val (lam e₁″) {{val-lam}}   , e₁⤅lam-e₁″ | e₂⇓           | e₃⇓           | ()
      sn (IF D₁ D₂ D₃) | val true      {{val-true}}  , e₁⤅true    | e₂′ , e₂⤅e₂′ | e₃⇓           | TRUE  = e₂′ , lem-if-true e₁⤅true e₂⤅e₂′
      sn (IF D₁ D₂ D₃) | val false     {{val-false}} , e₁⤅false   | e₂⇓           | e₃′ , e₃⤅e₃′ | FALSE = e₃′ , lem-if-false e₁⤅false e₃⤅e₃′


--------------------------------------------------------------------------------
