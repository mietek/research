{-# OPTIONS --rewriting #-}

module StdLPTT where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import S4TTTerms
open import S4TTTermsLemmas


--------------------------------------------------------------------------------


-- TODO: unfinished
-- infixr 8 _⊃_
-- data Form : Nat → Set
--   where
--     BASE : ∀ {d} → Form d
--     _⊃_  : ∀ {d} → Form d → Form d → Form d
--     [_]_ : ∀ {d} → Term₁ d → Form d → Form d


-- --------------------------------------------------------------------------------


-- MRENₚ : ∀ {d d′} → d′ ≥ d → Form d
--                  → Form d′
-- MRENₚ e BASE      = BASE
-- MRENₚ e (A ⊃ B)   = MRENₚ e A ⊃ MRENₚ e B
-- MRENₚ e ([ M ] A) = [ MREN e M ] MRENₚ e A


-- MWKₚ : ∀ {d} → Form d
--              → Form (suc d)
-- MWKₚ A = MRENₚ (drop id≥) A


-- MSUBₚ : ∀ {d n} → Terms₁ d n → Form n
--                 → Form d
-- MSUBₚ x BASE      = BASE
-- MSUBₚ x (A ⊃ B)   = MSUBₚ x A ⊃ MSUBₚ x B
-- MSUBₚ x ([ M ] A) = [ MSUB x M ] MSUBₚ x A


-- MCUTₚ : ∀ {d} → Term₁ d → Form (suc d)
--               → Form d
-- MCUTₚ M A = MSUBₚ (MIDS₁ , M) A


-- --------------------------------------------------------------------------------


-- id-MRENₚ : ∀ {d} → (A : Form d)
--                  → MRENₚ id≥ A ≡ A
-- id-MRENₚ BASE      = refl
-- id-MRENₚ (A ⊃ B)   = _⊃_ & id-MRENₚ A ⊗ id-MRENₚ B
-- id-MRENₚ ([ M ] A) = [_]_ & id-MREN M ⊗ id-MRENₚ A


-- comp-MRENₚ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (A : Form d)
--                          → MRENₚ (e₁ ∘≥ e₂) A ≡ MRENₚ e₂ (MRENₚ e₁ A)
-- comp-MRENₚ e₁ e₂ BASE      = refl
-- comp-MRENₚ e₁ e₂ (A ⊃ B)   = _⊃_ & comp-MRENₚ e₁ e₂ A ⊗ comp-MRENₚ e₁ e₂ B
-- comp-MRENₚ e₁ e₂ ([ M ] A) = [_]_ & comp-MREN e₁ e₂ M ⊗ comp-MRENₚ e₁ e₂ A


-- --------------------------------------------------------------------------------


-- infix 7 _true
-- record Truth (d : Nat) : Set
--   where
--     constructor _true
--     field
--       A : Form d


-- --------------------------------------------------------------------------------


-- MRENₜ : ∀ {d d′} → d′ ≥ d → Truth d
--                  → Truth d′
-- MRENₜ e (A true) = MRENₚ e A true


-- MWKₜ : ∀ {d} → Truth d
--              → Truth (suc d)
-- MWKₜ (A true) = MWKₚ A true


-- MSUBₜ : ∀ {d n} → Terms₁ d n → Truth n
--                 → Truth d
-- MSUBₜ x (A true) = MSUBₚ x A true


-- MCUTₜ : ∀ {d} → Term₁ d → Truth (suc d)
--               → Truth d
-- MCUTₜ M (A true) = MCUTₚ M A true


-- --------------------------------------------------------------------------------


-- id-MRENₜ : ∀ {d} → (Aₜ : Truth d)
--                  → MRENₜ id≥ Aₜ ≡ Aₜ
-- id-MRENₜ (A true) = _true & id-MRENₚ A


-- comp-MRENₜ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Aₜ : Truth d)
--                          → MRENₜ (e₁ ∘≥ e₂) Aₜ ≡ MRENₜ e₂ (MRENₜ e₁ Aₜ)
-- comp-MRENₜ e₁ e₂ (A true) = _true & comp-MRENₚ e₁ e₂ A


-- --------------------------------------------------------------------------------


-- Truths : Nat → Nat → Set
-- Truths d g = Vec (Truth d) g


-- --------------------------------------------------------------------------------


-- MRENSₜ : ∀ {d d′ g} → d′ ≥ d → Truths d g
--                     → Truths d′ g
-- MRENSₜ e Γ = MAPS (MRENₜ e) Γ


-- MWKSₜ : ∀ {d g} → Truths d g
--                 → Truths (suc d) g
-- MWKSₜ Γ = MAPS MWKₜ Γ


-- --------------------------------------------------------------------------------


-- id-MRENSₜ : ∀ {d g} → (Γ : Truths d g)
--                     → MRENSₜ id≥ Γ ≡ Γ
-- id-MRENSₜ ∙        = refl
-- id-MRENSₜ (Γ , Aₜ) = _,_ & id-MRENSₜ Γ ⊗ id-MRENₜ Aₜ


-- comp-MRENSₜ : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Γ : Truths d g)
--                             → MRENSₜ (e₁ ∘≥ e₂) Γ ≡ MRENSₜ e₂ (MRENSₜ e₁ Γ)
-- comp-MRENSₜ e₁ e₂ ∙        = refl
-- comp-MRENSₜ e₁ e₂ (Γ , Aₜ) = _,_ & comp-MRENSₜ e₁ e₂ Γ ⊗ comp-MRENₜ e₁ e₂ Aₜ


-- resp-MRENSₜ-⊇ : ∀ {d d′ g g′ e₂} → {Γ : Truths d g} {Γ′ : Truths d g′}
--                                  → (e₁ : d′ ≥ d) → Γ′ ⊇⟨ e₂ ⟩ Γ
--                                  → MRENSₜ e₁ Γ′ ⊇⟨ e₂ ⟩ MRENSₜ e₁ Γ
-- resp-MRENSₜ-⊇ e₁ done     = done
-- resp-MRENSₜ-⊇ e₁ (drop η) = resp-MRENSₜ-⊇ e₁ η ∘⊇ drop id⊇
-- resp-MRENSₜ-⊇ e₁ (keep η) = keep (resp-MRENSₜ-⊇ e₁ η)


-- resp-MWKSₜ-⊇ : ∀ {d g g′ e} → {Γ : Truths d g} {Γ′ : Truths d g′}
--                             → Γ′ ⊇⟨ e ⟩ Γ
--                             → MWKSₜ Γ′ ⊇⟨ e ⟩ MWKSₜ Γ
-- resp-MWKSₜ-⊇ η = resp-MRENSₜ-⊇ (drop id≥) η


-- resp-MRENSₜ-∋ : ∀ {d d′ g i} → {Γ : Truths d g} {A : Form d}
--                              → (e : d′ ≥ d) → Γ ∋⟨ i ⟩ A true
--                              → MRENSₜ e Γ ∋⟨ i ⟩ MRENₚ e A true
-- resp-MRENSₜ-∋ e zero    = zero
-- resp-MRENSₜ-∋ e (suc 𝒾) = suc (resp-MRENSₜ-∋ e 𝒾)


-- resp-MWKSₜ-∋ : ∀ {d g i} → {Γ : Truths d g} {A : Form d}
--                          → Γ ∋⟨ i ⟩ A true
--                          → MWKSₜ Γ ∋⟨ i ⟩ MWKₚ A true
-- resp-MWKSₜ-∋ 𝒾 = resp-MRENSₜ-∋ (drop id≥) 𝒾


-- --------------------------------------------------------------------------------


-- infix 7 _valid
-- record Validity (d : Nat) : Set
--   where
--     constructor _valid
--     field
--       A : Form d


-- --------------------------------------------------------------------------------


-- MRENᵥ : ∀ {d d′} → d′ ≥ d → Validity d
--                  → Validity d′
-- MRENᵥ e (A valid) = MRENₚ e A valid


-- MWKᵥ : ∀ {d} → Validity d
--              → Validity (suc d)
-- MWKᵥ (A valid) = MWKₚ A valid


-- MSUBᵥ : ∀ {d n} → Terms₁ d n → Validity n
--                 → Validity d
-- MSUBᵥ x (A valid) = MSUBₚ x A valid


-- MCUTᵥ : ∀ {d} → Term₁ d → Validity (suc d)
--               → Validity d
-- MCUTᵥ M (A valid) = MCUTₚ M A valid


-- --------------------------------------------------------------------------------


-- id-MRENᵥ : ∀ {d} → (Aᵥ : Validity d)
--                  → MRENᵥ id≥ Aᵥ ≡ Aᵥ
-- id-MRENᵥ (A valid) = _valid & id-MRENₚ A


-- comp-MRENᵥ : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Aᵥ : Validity d)
--                          → MRENᵥ (e₁ ∘≥ e₂) Aᵥ ≡ MRENᵥ e₂ (MRENᵥ e₁ Aᵥ)
-- comp-MRENᵥ e₁ e₂ (A valid) = _valid & comp-MRENₚ e₁ e₂ A


-- --------------------------------------------------------------------------------


-- data Validities : Nat → Set
--   where
--     ∙ : Validities zero

--     _,_ : ∀ {d} → Validities d → Validity d
--                 → Validities (suc d)


-- --------------------------------------------------------------------------------


-- infix 4 _⊇⟪_⟫_
-- data _⊇⟪_⟫_ : ∀ {d d′} → Validities d′ → d′ ≥ d → Validities d → Set
--   where
--     done : ∙ ⊇⟪ done ⟫ ∙

--     drop : ∀ {d d′ e} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d′}
--                       → Δ′ ⊇⟪ e ⟫ Δ
--                       → Δ′ , Aᵥ ⊇⟪ drop e ⟫ Δ

--     keep : ∀ {d d′ e} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d}
--                          {Aᵥ° : Validity d′} {{_ : MRENᵥ e Aᵥ ≡ Aᵥ°}}
--                       → Δ′ ⊇⟪ e ⟫ Δ
--                       → Δ′ , Aᵥ° ⊇⟪ keep e ⟫ Δ , Aᵥ


-- id⊇◈ : ∀ {d} → {Δ : Validities d}
--              → Δ ⊇⟪ id≥ ⟫ Δ
-- id⊇◈ {Δ = ∙}      = done
-- id⊇◈ {Δ = Δ , Aᵥ} = keep {{id-MRENᵥ Aᵥ}} id⊇◈


-- _∘⊇◈_ : ∀ {d d′ d″ e₁ e₂} → {Δ : Validities d} {Δ′ : Validities d′} {Δ″ : Validities d″}
--                           → Δ′ ⊇⟪ e₁ ⟫ Δ → Δ″ ⊇⟪ e₂ ⟫ Δ′
--                           → Δ″ ⊇⟪ e₁ ∘≥ e₂ ⟫ Δ
-- η₁      ∘⊇◈ done    = η₁
-- η₁      ∘⊇◈ drop η₂ = drop (η₁ ∘⊇◈ η₂)
-- drop η₁ ∘⊇◈ keep η₂ = drop (η₁ ∘⊇◈ η₂)
-- keep {e = e₁} {Aᵥ = Aᵥ} {{refl}} η₁ ∘⊇◈ keep {e = e₂} {{refl}} η₂
--   = keep {{comp-MRENᵥ e₁ e₂ Aᵥ}} (η₁ ∘⊇◈ η₂)


-- --------------------------------------------------------------------------------


-- infix 4 _∋⟪_⟫_
-- data _∋⟪_⟫_ : ∀ {d} → Validities d → Fin d → Validity d → Set
--   where
--     zero : ∀ {d} → {Δ : Validities d} {Aᵥ : Validity d}
--                     {Aᵥ° : Validity (suc d)} {{_ : MWKᵥ Aᵥ ≡ Aᵥ°}}
--                  → Δ , Aᵥ ∋⟪ zero ⟫ Aᵥ°

--     suc : ∀ {d i} → {Δ : Validities d} {Aᵥ : Validity d} {Bᵥ : Validity d}
--                      {Aᵥ° : Validity (suc d)} {{_ : MWKᵥ Aᵥ ≡ Aᵥ°}}
--                   → Δ ∋⟪ i ⟫ Aᵥ
--                   → Δ , Bᵥ ∋⟪ suc i ⟫ Aᵥ°


-- ren∋◈ : ∀ {d d′ e i} → {Δ : Validities d} {Δ′ : Validities d′} {Aᵥ : Validity d}
--                      → Δ′ ⊇⟪ e ⟫ Δ → Δ ∋⟪ i ⟫ Aᵥ
--                      → Δ′ ∋⟪ REN∋ e i ⟫ MRENᵥ e Aᵥ
-- ren∋◈ {i = i} {Aᵥ = Aᵥ} done 𝒾             = coerce 𝒾 ((\ Aᵥ′ → ∙ ∋⟪ i ⟫ Aᵥ′) & id-MRENᵥ Aᵥ ⁻¹)
-- ren∋◈         {Aᵥ = Aᵥ} (drop {e = e} η) 𝒾 = suc {{comp-MRENᵥ e (drop id≥) Aᵥ ⁻¹}} (ren∋◈ η 𝒾)
-- ren∋◈                   (keep {e = e} {Aᵥ = Aᵥ} {{refl}} η) (zero {{refl}})
--   = zero {{ comp-MRENᵥ e (drop id≥) Aᵥ ⁻¹
--           ⋮ comp-MRENᵥ (drop id≥) (keep e) Aᵥ
--          }}
-- ren∋◈                   (keep {e = e} {{refl}} η) (suc {Aᵥ = Aᵥ} {{refl}} 𝒾)
--   = suc {{ comp-MRENᵥ e (drop id≥) Aᵥ ⁻¹
--          ⋮ comp-MRENᵥ (drop id≥) (keep e) Aᵥ
--         }} (ren∋◈ η 𝒾)


-- --------------------------------------------------------------------------------


-- infix 4 _⊢_⦂_
-- record Derivation (d : Nat) : Set
--   where
--     constructor _⊢_⦂_
--     field
--       {g} : Nat
--       Γ   : Truths d g
--       M   : Term d g
--       Aₜ  : Truth d


-- infix 3 _⨾_
-- data _⨾_ : ∀ {d} → Validities d → Derivation d → Set
--   where
--     var : ∀ {d g i} → {Δ : Validities d} {Γ : Truths d g}
--                        {A : Form d}
--                     → Γ ∋⟨ i ⟩ A true
--                     → Δ ⨾ Γ ⊢ VAR i ⦂ A true

--     lam : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
--                        {A B : Form d}
--                     → Δ ⨾ Γ , A true ⊢ M ⦂ B true
--                     → Δ ⨾ Γ ⊢ LAM M ⦂ A ⊃ B true

--     app : ∀ {d g M N} → {Δ : Validities d} {Γ : Truths d g}
--                          {A B : Form d}
--                       → Δ ⨾ Γ ⊢ M ⦂ A ⊃ B true → Δ ⨾ Γ ⊢ N ⦂ A true
--                       → Δ ⨾ Γ ⊢ APP M N ⦂ B true

--     mvar : ∀ {d g i} → {Δ : Validities d} {Γ : Truths d g}
--                         {A : Form d}
--                      → Δ ∋⟪ i ⟫ A valid
--                      → Δ ⨾ Γ ⊢ MVAR i ⦂ A true

--     box : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
--                        {A : Form d}
--                     → Δ ⨾ ∙ ⊢ M ⦂ A true
--                     → Δ ⨾ Γ ⊢ BOX M ⦂ [ M ] A true

--     letbox : ∀ {d g M N O} → {Δ : Validities d} {Γ : Truths d g}
--                               {A : Form d} {B : Form (suc d)}
--                               {Γ° : Truths (suc d) g} {{_ : Γ° ≡ MWKSₜ Γ}}
--                               {B° : Form d} {{_ : B° ≡ MCUTₚ O B}}
--                            → Δ ⨾ Γ ⊢ M ⦂ [ O ] A true → Δ , A valid ⨾ Γ° ⊢ N ⦂ B true
--                            → Δ ⨾ Γ ⊢ LETBOX M N ⦂ B° true


-- --------------------------------------------------------------------------------


-- ren : ∀ {d g g′ e M} → {Δ : Validities d} {Γ : Truths d g} {Γ′ : Truths d g′}
--                         {A : Form d}
--                      → Γ′ ⊇⟨ e ⟩ Γ → Δ ⨾ Γ ⊢ M ⦂ A true
--                      → Δ ⨾ Γ′ ⊢ REN e M ⦂ A true
-- ren η (var 𝒾)   = var (ren∋ η 𝒾)
-- ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
-- ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)
-- ren η (mvar 𝒾)  = mvar 𝒾
-- ren η (box 𝒟)   = box 𝒟
-- ren η (letbox {{refl}} {{refl}} 𝒟 ℰ)
--   = letbox {{refl}} {{refl}} (ren η 𝒟) (ren (resp-MWKSₜ-⊇ η) ℰ)


-- wk : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
--                   {A B : Form d}
--                → Δ ⨾ Γ ⊢ M ⦂ A true
--                → Δ ⨾ Γ , B true ⊢ WK M ⦂ A true
-- wk 𝒟 = ren (drop id⊇) 𝒟


-- vz : ∀ {d g} → {Δ : Validities d} {Γ : Truths d g}
--                 {A : Form d}
--              → Δ ⨾ Γ , A true ⊢ VZ ⦂ A true
-- vz = var zero


-- --------------------------------------------------------------------------------


-- comp-MWKₚ-MRENₚ-keep : ∀ {d d′} → (e : d′ ≥ d) (A : Form d)
--                                 → (MRENₚ (keep e) ∘ MWKₚ) A ≡ (MWKₚ ∘ MRENₚ e) A
-- comp-MWKₚ-MRENₚ-keep e A = comp-MRENₚ (drop id≥) (keep e) A ⁻¹
--                          ⋮ (\ e′ → MRENₚ (drop e′) A) & (lid∘ e ⋮ rid∘ e ⁻¹)
--                          ⋮ comp-MRENₚ e (drop id≥) A


-- comp-MWKSₜ-MRENSₜ-keep : ∀ {d d′ g} → (e : d′ ≥ d) (Γ : Truths d g)
--                                     → (MRENSₜ (keep e) ∘ MWKSₜ) Γ ≡ (MWKSₜ ∘ MRENSₜ e) Γ
-- comp-MWKSₜ-MRENSₜ-keep e ∙            = refl
-- comp-MWKSₜ-MRENSₜ-keep e (Γ , A true) = _,_ & comp-MWKSₜ-MRENSₜ-keep e Γ
--                                             ⊗ _true & comp-MWKₚ-MRENₚ-keep e A


-- comp-MRENₚ-MSUBₚ : ∀ {d d′ n} → (e : d′ ≥ d) (x : Terms₁ d n) (A : Form n)
--                               → MSUBₚ (MRENS₁ e x) A ≡ (MRENₚ e ∘ MSUBₚ x) A
-- comp-MRENₚ-MSUBₚ e x BASE      = refl
-- comp-MRENₚ-MSUBₚ e x (A ⊃ B)   = _⊃_ & comp-MRENₚ-MSUBₚ e x A ⊗ comp-MRENₚ-MSUBₚ e x B
-- comp-MRENₚ-MSUBₚ e x ([ M ] A) = [_]_ & comp-MREN-MSUB e x M ⊗ comp-MRENₚ-MSUBₚ e x A


-- comp-MSUBₚ-MRENₚ : ∀ {d n n′} → (x : Terms₁ d n′) (e : n′ ≥ n) (A : Form n)
--                               → MSUBₚ (GETS x e) A ≡ (MSUBₚ x ∘ MRENₚ e) A
-- comp-MSUBₚ-MRENₚ x e BASE      = refl
-- comp-MSUBₚ-MRENₚ x e (A ⊃ B)   = _⊃_ & comp-MSUBₚ-MRENₚ x e A ⊗ comp-MSUBₚ-MRENₚ x e B
-- comp-MSUBₚ-MRENₚ x e ([ M ] A) = [_]_ & comp-MSUB-MREN x e M ⊗ comp-MSUBₚ-MRENₚ x e A


-- oops : ∀ {d d′} → (e : d′ ≥ d)
--                 → MRENS e MIDS₁ ≡ GETS MIDS₁ e
-- oops done     = refl
-- oops (drop e) = comp-MRENS e (drop id≥) MIDS₁
--               ⋮ MWKS & oops e
--               ⋮ comp-MRENS-GETS (drop id≥) MIDS₁ e ⁻¹
-- oops (keep e) = (_, MVZ) & ( comp-MWKS-MRENS-keep e MIDS₁
--                            ⋮ MWKS & oops e
--                            ⋮ comp-MRENS-GETS (drop id≥) MIDS₁ e ⁻¹
--                            )


-- mren : ∀ {d d′ g e M} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths d g}
--                          {A : Form d}
--                       → Δ′ ⊇⟪ e ⟫ Δ → Δ ⨾ Γ ⊢ M ⦂ A true
--                       → Δ′ ⨾ MRENSₜ e Γ ⊢ MREN e M ⦂ MRENₚ e A true
-- mren η (var 𝒾)   = var (resp-MRENSₜ-∋ _ 𝒾)
-- mren η (lam 𝒟)   = lam (mren η 𝒟)
-- mren η (app 𝒟 ℰ) = app (mren η 𝒟) (mren η ℰ)
-- mren η (mvar 𝒾)  = mvar (ren∋◈ η 𝒾)
-- mren η (box 𝒟)   = box (mren η 𝒟)
-- mren {e = e} η (letbox {O = O} {Γ = Γ} {A = A} {B} {{refl}} {{refl}} 𝒟 ℰ)
--   = letbox
--       {{comp-MWKSₜ-MRENSₜ-keep e Γ}}
--       {{( comp-MRENₚ-MSUBₚ e (MIDS₁ , O) B ⁻¹
--         ⋮ (\ x′ → MSUBₚ (x′ , MREN e O) B) & oops e
--         ⋮ comp-MSUBₚ-MRENₚ (MIDS₁ , MREN e O) (keep e) B
--         )}}
--       (mren η 𝒟)
--       (mren (keep {{refl}} η) ℰ)


-- mwk : ∀ {d g M} → {Δ : Validities d} {Γ : Truths d g}
--                    {A B : Form d}
--                 → Δ ⨾ Γ ⊢ M ⦂ A true
--                 → Δ , B valid ⨾ MWKSₜ Γ ⊢ MWK M ⦂ MWKₚ A true
-- mwk 𝒟 = mren (drop id⊇◈) 𝒟


-- mvz : ∀ {d g} → {Δ : Validities d} {Γ : Truths d g}
--                  {A : Form d}
--               → Δ , A valid ⨾ MWKSₜ Γ ⊢ MVZ ⦂ MWKₚ A true
-- mvz = mvar zero


-- --------------------------------------------------------------------------------
