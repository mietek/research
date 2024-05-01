module A201801.LPTTTypesLemmas where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.S4TTTerms
open import A201801.S4TTTermsLemmas
open import A201801.LPTTTypes


--------------------------------------------------------------------------------
{-
                            TMREN id A ≡ A                                      id-TMREN
                           TMRENS id Ξ ≡ Ξ                                      id-TMRENS
                     TMREN (e₁ ∘ e₂) A ≡ (TMREN e₂ ∘ TMREN e₁) A                comp-TMREN
                    TMRENS (e₁ ∘ e₂) Ξ ≡ (TMRENS e₂ ∘ TMRENS e₁) Ξ              comp-TMRENS
                                                                                𝐓𝐌𝐑𝐄𝐍
                                                                                𝐓𝐌𝐑𝐄𝐍𝐒



                    TMSUB (GETS τ e) A ≡ (TMSUB τ ∘ TMREN e) A                  comp-TMSUB-TMREN
              (TMSUB (τ , M) ∘ TMWK) A ≡ TMSUB τ A                              id-cons-TMWK-TMSUB
            (TMSUBS (τ , M) ∘ TMWKS) Ξ ≡ TMSUBS τ Ξ                             id-cons-TMWKS-TMSUBS

                         TMSUB MIDS* A ≡ A                                      id-TMSUB
                        TMSUBS MIDS* Ξ ≡ Ξ                                      id-TMSUBS
                   TMSUB (MSUBS τ υ) A ≡ (TMSUB τ ∘ TMSUB υ) A                  comp-TMSUB
                  TMSUBS (MSUBS τ υ) Ξ ≡ (TMSUBS τ ∘ TMSUBS υ) Ξ                comp-TMSUBS
                                                                                𝐓𝐌𝐒𝐔𝐁
                                                                                𝐓𝐌𝐒𝐔𝐁𝐒
-}
--------------------------------------------------------------------------------


id-TMREN : ∀ {d} → (A : Type d)
                 → TMREN id A ≡ A
id-TMREN (ι P)     = refl
id-TMREN (A ⊃ B)   = _⊃_ & id-TMREN A ⊗ id-TMREN B
id-TMREN ([ M ] A) = [_]_ & id-MREN M ⊗ id-TMREN A


id-TMRENS : ∀ {d n} → (Ξ : Types d n)
                    → TMRENS id Ξ ≡ Ξ
id-TMRENS ∙       = refl
id-TMRENS (Ξ , A) = _,_ & id-TMRENS Ξ ⊗ id-TMREN A


comp-TMREN : ∀ {d d′ d″} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (A : Type d)
                         → TMREN (e₁ ∘ e₂) A ≡ (TMREN e₂ ∘ TMREN e₁) A
comp-TMREN e₁ e₂ (ι P)     = refl
comp-TMREN e₁ e₂ (A ⊃ B)   = _⊃_ & comp-TMREN e₁ e₂ A ⊗ comp-TMREN e₁ e₂ B
comp-TMREN e₁ e₂ ([ M ] A) = [_]_ & comp-MREN e₁ e₂ M ⊗ comp-TMREN e₁ e₂ A


comp-TMRENS : ∀ {d d′ d″ n} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (Ξ : Types d n)
                            → TMRENS (e₁ ∘ e₂) Ξ ≡ (TMRENS e₂ ∘ TMRENS e₁) Ξ
comp-TMRENS e₁ e₂ ∙       = refl
comp-TMRENS e₁ e₂ (Ξ , A) = _,_ & comp-TMRENS e₁ e₂ Ξ ⊗ comp-TMREN e₁ e₂ A


𝐓𝐌𝐑𝐄𝐍 : Presheaf 𝐆𝐄𝐐 Type
𝐓𝐌𝐑𝐄𝐍 = record
          { ℱ     = TMREN
          ; idℱ   = funext! id-TMREN
          ; compℱ = \ e₁ e₂ → funext! (comp-TMREN e₁ e₂)
          }


𝐓𝐌𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf 𝐆𝐄𝐐 (\ d → Types d n)
𝐓𝐌𝐑𝐄𝐍𝐒 = record
           { ℱ     = TMRENS
           ; idℱ   = funext! id-TMRENS
           ; compℱ = \ e₁ e₂ → funext! (comp-TMRENS e₁ e₂)
           }


--------------------------------------------------------------------------------


comp-TMWK-TMREN-drop : ∀ {d d′} → (e : d′ ≥ d) (A : Type d)
                                → TMREN (drop e) A ≡ (TMWK ∘ TMREN e) A
comp-TMWK-TMREN-drop e A = (\ e′ → TMREN (drop e′) A) & rid∘ e ⁻¹
                         ⋮ comp-TMREN e (drop id) A


comp-TMWK-TMREN-keep : ∀ {d d′} → (e : d′ ≥ d) (A : Type d)
                                → (TMREN (keep e) ∘ TMWK) A ≡ (TMWK ∘ TMREN e) A
comp-TMWK-TMREN-keep e A = comp-TMREN (drop id) (keep e) A ⁻¹
                         ⋮ (\ e′ → TMREN (drop e′) A) & (lid∘ e ⋮ rid∘ e ⁻¹)
                         ⋮ comp-TMREN e (drop id) A


comp-TMWKS-TMRENS-keep : ∀ {d d′ n} → (e : d′ ≥ d) (Ξ : Types d n)
                                    → (TMRENS (keep e) ∘ TMWKS) Ξ ≡ (TMWKS ∘ TMRENS e) Ξ
comp-TMWKS-TMRENS-keep e ∙       = refl
comp-TMWKS-TMRENS-keep e (Ξ , A) = _,_ & comp-TMWKS-TMRENS-keep e Ξ ⊗ comp-TMWK-TMREN-keep e A


--------------------------------------------------------------------------------


comp-TMSUB-TMREN : ∀ {d n n′} → (τ : Terms* d n′) (e : n′ ≥ n) (A : Type n)
                              → TMSUB (GETS τ e) A ≡ (TMSUB τ ∘ TMREN e) A
comp-TMSUB-TMREN τ e (ι P)     = refl
comp-TMSUB-TMREN τ e (A ⊃ B)   = _⊃_ & comp-TMSUB-TMREN τ e A ⊗ comp-TMSUB-TMREN τ e B
comp-TMSUB-TMREN τ e ([ M ] A) = [_]_ & comp-MSUB-MREN τ e M ⊗ comp-TMSUB-TMREN τ e A


id-cons-TMWK-TMSUB : ∀ {d n} → (τ : Terms* d n) (M : Term d zero) (A : Type n)
                             → (TMSUB (τ , M) ∘ TMWK) A ≡ TMSUB τ A
id-cons-TMWK-TMSUB τ M N = comp-TMSUB-TMREN (τ , M) (drop id) N ⁻¹
                         ⋮ (\ x′ → TMSUB x′ N) & id-GETS τ


id-cons-TMWKS-TMSUBS : ∀ {d n m} → (τ : Terms* d n) (M : Term d zero) (Ξ : Types n m)
                                 → (TMSUBS (τ , M) ∘ TMWKS) Ξ ≡ TMSUBS τ Ξ
id-cons-TMWKS-TMSUBS τ M ∙       = refl
id-cons-TMWKS-TMSUBS τ M (Ξ , A) = _,_ & id-cons-TMWKS-TMSUBS τ M Ξ ⊗ id-cons-TMWK-TMSUB τ M A


--------------------------------------------------------------------------------


id-TMSUB : ∀ {d} → (A : Type d)
                 → TMSUB MIDS* A ≡ A
id-TMSUB (ι P)     = refl
id-TMSUB (A ⊃ B)   = _⊃_ & id-TMSUB A ⊗ id-TMSUB B
id-TMSUB ([ M ] A) = [_]_ & id-MSUB M ⊗ id-TMSUB A


id-TMSUBS : ∀ {d n} → (Ξ : Types d n)
                    → TMSUBS MIDS* Ξ ≡ Ξ
id-TMSUBS ∙       = refl
id-TMSUBS (Ξ , A) = _,_ & id-TMSUBS Ξ ⊗ id-TMSUB A


comp-TMSUB : ∀ {d n m} → (τ : Terms* d n) (υ : Terms* n m) (A : Type m)
                       → TMSUB (MSUBS τ υ) A ≡ (TMSUB τ ∘ TMSUB υ) A
comp-TMSUB τ υ (ι P)     = refl
comp-TMSUB τ υ (A ⊃ B)   = _⊃_ & comp-TMSUB τ υ A ⊗ comp-TMSUB τ υ B
comp-TMSUB τ υ ([ M ] A) = [_]_ & comp-MSUB τ υ M ⊗ comp-TMSUB τ υ A


comp-TMSUBS : ∀ {d n m l} → (τ : Terms* d n) (υ : Terms* n m) (Ξ : Types m l)
                          → TMSUBS (MSUBS τ υ) Ξ ≡ (TMSUBS τ ∘ TMSUBS υ) Ξ
comp-TMSUBS τ υ ∙       = refl
comp-TMSUBS τ υ (Ξ , A) = _,_ & comp-TMSUBS τ υ Ξ ⊗ comp-TMSUB τ υ A


𝐓𝐌𝐒𝐔𝐁 : Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬* Type
𝐓𝐌𝐒𝐔𝐁 = record
          { ℱ     = TMSUB
          ; idℱ   = funext! id-TMSUB
          ; compℱ = \ υ τ → funext! (comp-TMSUB τ υ)
          }


𝐓𝐌𝐒𝐔𝐁𝐒 : ∀ {n} → Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬* (\ d → Types d n)
𝐓𝐌𝐒𝐔𝐁𝐒 = record
           { ℱ     = TMSUBS
           ; idℱ   = funext! id-TMSUBS
           ; compℱ = \ υ τ → funext! (comp-TMSUBS τ υ)
           }


--------------------------------------------------------------------------------
