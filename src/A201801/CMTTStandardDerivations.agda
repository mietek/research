{-# OPTIONS --rewriting #-}

module A201801.CMTTStandardDerivations where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.Vec
open import A201801.AllVec
open import A201801.CMTTScopes
open import A201801.CMTTTypes
open import A201801.CMTTTerms
import A201801.CMTTDerivations as CMTT


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢_⦂_true
  data _⨾_⊢_⦂_true : ∀ {d g} → {σ : Scopes d}
                              → Asserts σ → Types g → Term σ g → Type → Set
    where
      var : ∀ {A d g I} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                        → Γ ∋⟨ I ⟩ A
                        → Δ ⨾ Γ ⊢ VAR I ⦂ A true

      lam : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ (suc g)}
                        → Δ ⨾ Γ , A ⊢ M ⦂ B true
                        → Δ ⨾ Γ ⊢ LAM M ⦂ A ⊃ B true

      app : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M N : Term σ g}
                        → Δ ⨾ Γ ⊢ M ⦂ A ⊃ B true → Δ ⨾ Γ ⊢ N ⦂ A true
                        → Δ ⨾ Γ ⊢ APP M N ⦂ B true

      mvar : ∀ {A m d g I} → {σ : Scopes d}
                              {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                              {i : σ ∋⟨ I ⟩ m} {τ : Terms σ g m}
                           → Δ ∋◇⟨ i ⟩ ⟪ Ψ ⊫ A ⟫ → Δ ⨾ Γ ⊢ τ ⦂ Ψ alltrue
                           → Δ ⨾ Γ ⊢ MVAR i τ ⦂ A true

      box : ∀ {A m d g} → {σ : Scopes d}
                           {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ m}
                        → Δ ⨾ Ψ ⊢ M ⦂ A true
                        → Δ ⨾ Γ ⊢ BOX M ⦂ [ Ψ ] A true

      letbox : ∀ {A B m d g} → {σ : Scopes d}
                                {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                                {M : Term σ g} {N : Term (σ , m) g}
                             → Δ ⨾ Γ ⊢ M ⦂ [ Ψ ] A true → Δ , ⟪ Ψ ⊫ A ⟫ ⨾ Γ ⊢ N ⦂ B true
                             → Δ ⨾ Γ ⊢ LETBOX M N ⦂ B true

  infix 3 _⨾_⊢_⦂_alltrue
  _⨾_⊢_⦂_alltrue : ∀ {d g n} → {σ : Scopes d}
                              → Asserts σ → Types g → Terms σ g n → Types n → Set
  Δ ⨾ Γ ⊢ τ ⦂ Ξ alltrue = All (\ { (M , A) → Δ ⨾ Γ ⊢ M ⦂ A true }) (zip τ Ξ)


--------------------------------------------------------------------------------


mutual
  ↓ : ∀ {d g A} → {σ : Scopes d}
                   {Δ : Asserts σ} {Γ : Types g}
                   {M : Term σ g}
                → Δ ⨾ Γ ⊢ M ⦂ A true
                → Δ CMTT.⊢ M ⦂ A valid[ Γ ]
  ↓ (var i)      = CMTT.var i
  ↓ (lam 𝒟)      = CMTT.lam (↓ 𝒟)
  ↓ (app 𝒟 ℰ)    = CMTT.app (↓ 𝒟) (↓ ℰ)
  ↓ (mvar 𝑖 ψ)   = CMTT.mvar 𝑖 (↓ⁿ ψ)
  ↓ (box 𝒟)      = CMTT.box (↓ 𝒟)
  ↓ (letbox 𝒟 ℰ) = CMTT.letbox (↓ 𝒟) (↓ ℰ)

  ↓ⁿ : ∀ {d g n} → {σ : Scopes d}
                    {Δ : Asserts σ} {Γ : Types g}
                    {τ : Terms σ g n} {Ξ : Types n}
                 → Δ ⨾ Γ ⊢ τ ⦂ Ξ alltrue
                 → Δ CMTT.⊢ τ ⦂ Ξ allvalid[ Γ ]
  ↓ⁿ {τ = ∙}     {∙}     ∙       = ∙
  ↓ⁿ {τ = τ , M} {Ξ , A} (ξ , 𝒟) = ↓ⁿ ξ , ↓ 𝒟


mutual
  ↑ : ∀ {d g A} → {σ : Scopes d}
                   {Δ : Asserts σ} {Γ : Types g}
                   {M : Term σ g}
                → Δ CMTT.⊢ M ⦂ A valid[ Γ ]
                → Δ ⨾ Γ ⊢ M ⦂ A true
  ↑ (CMTT.var i)      = var i
  ↑ (CMTT.lam 𝒟)      = lam (↑ 𝒟)
  ↑ (CMTT.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
  ↑ (CMTT.mvar 𝑖 ψ)   = mvar 𝑖 (↑ⁿ ψ)
  ↑ (CMTT.box 𝒟)      = box (↑ 𝒟)
  ↑ (CMTT.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)

  ↑ⁿ : ∀ {d g n} → {σ : Scopes d}
                    {Δ : Asserts σ} {Γ : Types g}
                    {τ : Terms σ g n} {Ξ : Types n}
                 → Δ CMTT.⊢ τ ⦂ Ξ allvalid[ Γ ]
                 → Δ ⨾ Γ ⊢ τ ⦂ Ξ alltrue
  ↑ⁿ {τ = ∙}     {∙}     ∙       = ∙
  ↑ⁿ {τ = τ , M} {Ξ , A} (ξ , 𝒟) = ↑ⁿ ξ , ↑ 𝒟


mutual
  id↓↑ : ∀ {d g A} → {σ : Scopes d}
                      {Δ : Asserts σ} {Γ : Types g}
                      {M : Term σ g}
                   → (𝒟 : Δ CMTT.⊢ M ⦂ A valid[ Γ ])
                   → (↓ ∘ ↑) 𝒟 ≡ 𝒟
  id↓↑ (CMTT.var i)      = refl
  id↓↑ (CMTT.lam 𝒟)      = CMTT.lam & id↓↑ 𝒟
  id↓↑ (CMTT.app 𝒟 ℰ)    = CMTT.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ
  id↓↑ (CMTT.mvar 𝑖 ψ)   = CMTT.mvar 𝑖 & id↓ⁿ↑ⁿ ψ
  id↓↑ (CMTT.box 𝒟)      = CMTT.box & id↓↑ 𝒟
  id↓↑ (CMTT.letbox 𝒟 ℰ) = CMTT.letbox & id↓↑ 𝒟 ⊗ id↓↑ ℰ

  id↓ⁿ↑ⁿ : ∀ {d g n} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g}
                        {τ : Terms σ g n} {Ξ : Types n}
                     → (ξ : Δ CMTT.⊢ τ ⦂ Ξ allvalid[ Γ ])
                     → (↓ⁿ ∘ ↑ⁿ) ξ ≡ ξ
  id↓ⁿ↑ⁿ {τ = ∙}     {∙}     ∙       = refl
  id↓ⁿ↑ⁿ {τ = τ , M} {Ξ , A} (ξ , 𝒟) = _,_ & id↓ⁿ↑ⁿ ξ ⊗ id↓↑ 𝒟


mutual
  id↑↓ : ∀ {d g A} → {σ : Scopes d}
                      {Δ : Asserts σ} {Γ : Types g}
                      {M : Term σ g}
                   → (𝒟 : Δ ⨾ Γ ⊢ M ⦂ A true)
                   → (↑ ∘ ↓) 𝒟 ≡ 𝒟
  id↑↓ (var i)      = refl
  id↑↓ (lam 𝒟)      = lam & id↑↓ 𝒟
  id↑↓ (app 𝒟 ℰ)    = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ
  id↑↓ (mvar 𝑖 ψ)   = mvar 𝑖 & id↑ⁿ↓ⁿ ψ
  id↑↓ (box 𝒟)      = box & id↑↓ 𝒟
  id↑↓ (letbox 𝒟 ℰ) = letbox & id↑↓ 𝒟 ⊗ id↑↓ ℰ

  id↑ⁿ↓ⁿ : ∀ {d g n} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g}
                        {τ : Terms σ g n} {Ξ : Types n}
                     → (ξ : Δ ⨾ Γ ⊢ τ ⦂ Ξ alltrue)
                     → (↑ⁿ ∘ ↓ⁿ) ξ ≡ ξ
  id↑ⁿ↓ⁿ {τ = ∙}     {∙}     ∙       = refl
  id↑ⁿ↓ⁿ {τ = τ , M} {Ξ , A} (ξ , 𝒟) = _,_ & id↑ⁿ↓ⁿ ξ ⊗ id↑↓ 𝒟


--------------------------------------------------------------------------------
