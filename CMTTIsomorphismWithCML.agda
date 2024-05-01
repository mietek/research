{-# OPTIONS --rewriting #-}

module A201801.CMTTIsomorphismWithCML where

open import A201801.Prelude
open import A201801.Fin
open import A201801.List
open import A201801.AllList
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec
open import A201801.AllVecLemmas
open import A201801.CMTTScopes
open import A201801.CMTTTypes
open import A201801.CMTTTerms
open import A201801.CMTTDerivations
import A201801.CMLPropositions as CML
import A201801.CMLStandardDerivations as CML


--------------------------------------------------------------------------------


mutual
  ↓ₚ : Type → CML.Form
  ↓ₚ (ι P)     = CML.ι P
  ↓ₚ (A ⊃ B)   = ↓ₚ A CML.⊃ ↓ₚ B
  ↓ₚ ([ Ψ ] A) = CML.[ ↓ₚₛ Ψ ] ↓ₚ A

  ↓ₚₛ : ∀ {n} → Types n → List CML.Form
  ↓ₚₛ ∙       = ∙
  ↓ₚₛ (Ξ , A) = ↓ₚₛ Ξ , ↓ₚ A


↓ₐ : ∀ {g} → Assert g
           → CML.Assert
↓ₐ ⟪ Γ ⊫ A ⟫ = CML.⟪ ↓ₚₛ Γ ⊫ ↓ₚ A ⟫


↓ₐₛ : ∀ {d} → {σ : Scopes d}
            → Asserts σ
            → List CML.Assert
↓ₐₛ ∙                = ∙
↓ₐₛ (Δ , ⟪ Γ ⊫ A ⟫) = ↓ₐₛ Δ , ↓ₐ ⟪ Γ ⊫ A ⟫


↓∋ₚ : ∀ {g I A} → {Γ : Types g}
                → Γ ∋⟨ I ⟩ A
                → ↓ₚₛ Γ ∋ ↓ₚ A
↓∋ₚ zero    = zero
↓∋ₚ (suc i) = suc (↓∋ₚ i)


↓∋ₐ : ∀ {d m I A} → {σ : Scopes d} {i : σ ∋⟨ I ⟩ m}
                     {Δ : Asserts σ} {Ψ : Types m}
                  → Δ A201801.AllVec.∋◇⟨ i ⟩ ⟪ Ψ ⊫ A ⟫
                  → ↓ₐₛ Δ ∋ ↓ₐ ⟪ Ψ ⊫ A ⟫
↓∋ₐ zero    = zero
↓∋ₐ (suc i) = suc (↓∋ₐ i)


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_⦂_match[_]_
  data _⊢_⦂_match[_]_ : ∀ {d g} → {σ : Scopes d}
                                 → (Δ : Asserts σ) → Term σ g → (A : Type) (Γ : Types g)
                                 → ↓ₐₛ Δ CML.⊢ ↓ₚ A valid[ ↓ₚₛ Γ ] → Set
    where
      var : ∀ {A d g I} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                        → (i : Γ ∋⟨ I ⟩ A)
                        → Δ ⊢ VAR I ⦂ A match[ Γ ] CML.var (↓∋ₚ i)

      lam : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ (suc g)}
                           {𝒟 : _}
                        → Δ ⊢ M ⦂ B match[ Γ , A ] 𝒟
                        → Δ ⊢ LAM M ⦂ A ⊃ B match[ Γ ] CML.lam 𝒟

      app : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M N : Term σ g}
                           {𝒟 : _} {ℰ : _}
                        → Δ ⊢ M ⦂ A ⊃ B match[ Γ ] 𝒟 → Δ ⊢ N ⦂ A match[ Γ ] ℰ
                        → Δ ⊢ APP M N ⦂ B match[ Γ ] CML.app 𝒟 ℰ

      -- TODO: unfinished
      -- mvar : ∀ {A m d g I} → {σ : Scopes d}
      --                         {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
      --                         {i : σ ∋⟨ I ⟩ m} {υ : Terms σ g m}
      --                      → Δ AllVec.∋◇⟨ i ⟩ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ υ ⦂ Ψ allmatch[ Γ ] {!!}
      --                      → Δ ⊢ MVAR i υ ⦂ A match[ Γ ] CML.mvar {!i!} {!!}

      box : ∀ {A m d g} → {σ : Scopes d}
                           {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ m}
                           {𝒟 : _}
                        → Δ ⊢ M ⦂ A match[ Ψ ] 𝒟
                        → Δ ⊢ BOX M ⦂ [ Ψ ] A match[ Γ ] CML.box 𝒟

      letbox : ∀ {A B m d g} → {σ : Scopes d}
                                {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                                {M : Term σ g} {N : Term (σ , m) g}
                                {𝒟 : _} {ℰ : _}
                             → Δ ⊢ M ⦂ [ Ψ ] A match[ Γ ] 𝒟 → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ N ⦂ B match[ Γ ] ℰ
                             → Δ ⊢ LETBOX M N ⦂ B match[ Γ ] CML.letbox 𝒟 ℰ

  infix 3 _⊢_⦂_allmatch[_]_
  _⊢_⦂_allmatch[_]_ : ∀ {d g n} → {σ : Scopes d}
                                 → (Δ : Asserts σ) → Terms σ g n → (Ξ : Types n) (Γ : Types g)
                                 → ↓ₐₛ Δ CML.⊢ ↓ₚₛ Ξ allvalid[ ↓ₚₛ Γ ] → Set
  Δ ⊢ ∙     ⦂ ∙       allmatch[ Γ ] ∙       = ⊤
  Δ ⊢ τ , M ⦂ (Ξ , A) allmatch[ Γ ] (ξ , 𝒟) = Δ ⊢ τ ⦂ Ξ allmatch[ Γ ] ξ × Δ ⊢ M ⦂ A match[ Γ ] 𝒟




--     var : ∀ {A d g Δ Γ i} → (I : Fin g)
--                           → Δ ⊢ VAR {d} (toFin i) ⦂ A match[ Γ ] CML.var i

--     lam : ∀ {A B d g Δ Γ 𝒟} → {M : Term d (suc g)}
--                             → Δ ⊢ M ⦂ B match[ Γ , A ] 𝒟
--                             → Δ ⊢ LAM M ⦂ A ⊃ B match[ Γ ] CML.lam 𝒟

--     app : ∀ {A B d g Δ Γ 𝒟 ℰ} → {M N : Term d g}
--                               → Δ ⊢ M ⦂ A ⊃ B match[ Γ ] 𝒟 → Δ ⊢ N ⦂ A match[ Γ ] ℰ
--                               → Δ ⊢ APP M N ⦂ B match[ Γ ] CML.app 𝒟 ℰ

--     mvar : ∀ {A d g Δ Γ i} → (I : Fin d)
--                            → Δ ⊢ MVAR {g = g} (toFin i) ⦂ A match[ Γ ] CML.mvar i

-- --     box : ∀ {A d g Δ Γ 𝒟} → {M : Term d zero}
-- --                           → Δ ⊢ M ⦂ A match[ ∙ ] 𝒟
-- --                           → Δ ⊢ BOX {g = g} M ⦂ □ A match[ Γ ] CML.box 𝒟

-- --     letbox : ∀ {A B d g Δ Γ 𝒟 ℰ} → {M : Term d g} {N : Term (suc d) g}
-- --                                  → Δ ⊢ M ⦂ □ A match[ Γ ] 𝒟 → Δ , ⟪⊫ A ⟫ ⊢ N ⦂ B match[ Γ ] ℰ
-- --                                  → Δ ⊢ LETBOX M N ⦂ B match[ Γ ] CML.letbox 𝒟 ℰ


-- -- -- --------------------------------------------------------------------------------


-- -- -- toTerm : ∀ {Δ Γ A} → Δ CML.⊢ A valid[ Γ ]
-- -- --                    → Term (len Δ) (len Γ)
-- -- -- toTerm (CML.var i)      = VAR (toFin i)
-- -- -- toTerm (CML.lam 𝒟)      = LAM (toTerm 𝒟)
-- -- -- toTerm (CML.app 𝒟 ℰ)    = APP (toTerm 𝒟) (toTerm ℰ)
-- -- -- toTerm (CML.mvar i)     = MVAR (toFin i)
-- -- -- toTerm (CML.box 𝒟)      = BOX (toTerm 𝒟)
-- -- -- toTerm (CML.letbox 𝒟 ℰ) = LETBOX (toTerm 𝒟) (toTerm ℰ)


-- -- -- instance
-- -- --   match-toTerm : ∀ {Δ Γ A} → (𝒟 : Δ CML.⊢ A valid[ Γ ])
-- -- --                            → Δ ⊢ toTerm 𝒟 ⦂ A match[ Γ ] 𝒟
-- -- --   match-toTerm (CML.var i)      = var (toFin i)
-- -- --   match-toTerm (CML.lam 𝒟)      = lam (match-toTerm 𝒟)
-- -- --   match-toTerm (CML.app 𝒟 ℰ)    = app (match-toTerm 𝒟) (match-toTerm ℰ)
-- -- --   match-toTerm (CML.mvar i)     = mvar (toFin i)
-- -- --   match-toTerm (CML.box 𝒟)      = box (match-toTerm 𝒟)
-- -- --   match-toTerm (CML.letbox 𝒟 ℰ) = letbox (match-toTerm 𝒟) (match-toTerm ℰ)


-- -- -- --------------------------------------------------------------------------------


-- -- -- ↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
-- -- --                 → Δ ⊢ M ⦂ A valid[ Γ ]
-- -- --                 → toList Δ CML.⊢ A valid[ toList Γ ]
-- -- -- ↓ (var i)      = CML.var (to∋ i)
-- -- -- ↓ (lam 𝒟)      = CML.lam (↓ 𝒟)
-- -- -- ↓ (app 𝒟 ℰ)    = CML.app (↓ 𝒟) (↓ ℰ)
-- -- -- ↓ (mvar i)     = CML.mvar (to∋ i)
-- -- -- ↓ (box 𝒟)      = CML.box (↓ 𝒟)
-- -- -- ↓ (letbox 𝒟 ℰ) = CML.letbox (↓ 𝒟) (↓ ℰ)


-- -- -- instance
-- -- --   match↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
-- -- --                        → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ])
-- -- --                        → toList Δ ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟
-- -- --   match↓ (var {I = I} i)  = var I
-- -- --   match↓ (lam 𝒟)          = lam (match↓ 𝒟)
-- -- --   match↓ (app 𝒟 ℰ)        = app (match↓ 𝒟) (match↓ ℰ)
-- -- --   match↓ (mvar {I = I} i) = mvar I
-- -- --   match↓ (box 𝒟)          = box (match↓ 𝒟)
-- -- --   match↓ (letbox 𝒟 ℰ)     = letbox (match↓ 𝒟) (match↓ ℰ)


-- -- -- ↑ : ∀ {Δ Γ M A} → (𝒟 : Δ CML.⊢ A valid[ Γ ]) {{p : Δ ⊢ M ⦂ A match[ Γ ] 𝒟}}
-- -- --                 → fromList Δ ⊢ M ⦂ A valid[ fromList Γ ]
-- -- -- ↑ (CML.var i)      {{var I}}      = var (from∋ i)
-- -- -- ↑ (CML.lam 𝒟)      {{lam p}}      = lam (↑ 𝒟 {{p}})
-- -- -- ↑ (CML.app 𝒟 ℰ)    {{app p q}}    = app (↑ 𝒟 {{p}}) (↑ ℰ {{q}})
-- -- -- ↑ (CML.mvar i)     {{mvar I}}     = mvar (from∋ i)
-- -- -- ↑ (CML.box 𝒟)      {{box p}}      = box (↑ 𝒟 {{p}})
-- -- -- ↑ (CML.letbox 𝒟 ℰ) {{letbox p q}} = letbox (↑ 𝒟 {{p}}) (↑ ℰ {{q}})


-- -- -- --------------------------------------------------------------------------------


-- -- -- gen-id↓↑ : ∀ {Δ Γ M A} → (𝒟 : Δ CML.⊢ A valid[ Γ ]) {{p : Δ ⊢ M ⦂ A match[ Γ ] 𝒟}}
-- -- --                        → ↓ (↑ 𝒟 {{p}}) ≡ 𝒟
-- -- -- gen-id↓↑ (CML.var i)      {{var I}}      = refl
-- -- -- gen-id↓↑ (CML.lam 𝒟)      {{lam p}}      = CML.lam & gen-id↓↑ 𝒟 {{p}}
-- -- -- gen-id↓↑ (CML.app 𝒟 ℰ)    {{app p q}}    = CML.app & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}
-- -- -- gen-id↓↑ (CML.mvar i)     {{mvar I}}     = refl
-- -- -- gen-id↓↑ (CML.box 𝒟)      {{box p}}      = CML.box & gen-id↓↑ 𝒟 {{p}}
-- -- -- gen-id↓↑ (CML.letbox 𝒟 ℰ) {{letbox p q}} = CML.letbox & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}


-- -- -- id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ CML.⊢ A valid[ Γ ])
-- -- --                  → ↓ (↑ 𝒟) ≡ 𝒟
-- -- -- id↓↑ 𝒟 = gen-id↓↑ 𝒟 {{match-toTerm 𝒟}}


-- -- -- gen-id↑↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
-- -- --                        → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ]) {{p : toList Δ ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟}}
-- -- --                        → ↑ (↓ 𝒟) {{p}} ≡ 𝒟
-- -- -- gen-id↑↓ (var i)      {{var I}}      = refl
-- -- -- gen-id↑↓ (lam 𝒟)      {{lam p}}      = lam & gen-id↑↓ 𝒟 {{p}}
-- -- -- gen-id↑↓ (app 𝒟 ℰ)    {{app p q}}    = app & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}
-- -- -- gen-id↑↓ (mvar i)     {{mvar I}}     = refl
-- -- -- gen-id↑↓ (box 𝒟)      {{box p}}      = box & gen-id↑↓ 𝒟 {{p}}
-- -- -- gen-id↑↓ (letbox 𝒟 ℰ) {{letbox p q}} = letbox & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}


-- -- -- id↑↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
-- -- --                    → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ])
-- -- --                    → ↑ (↓ 𝒟) ≡ 𝒟
-- -- -- id↑↓ 𝒟 = gen-id↑↓ 𝒟 {{match↓ 𝒟}}


-- -- -- --------------------------------------------------------------------------------
