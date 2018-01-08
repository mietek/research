module StdS4LemmasScratch where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open GetAllList
open import AllListLemmas
open GetsAllList
open import StdS4
open import StdS4Lemmas


--------------------------------------------------------------------------------
{-
                     msub (gets ξ η) 𝒟 ≡ (msub ξ ∘ mren η) 𝒟                    comp-msub-mren

              msubs₁ (ξ , 𝒟) (mwks₁ ψ) ≡ msubs₁ ξ ψ                             expand-msubs₁

                   msub (mrens₁ η ξ) 𝒟 ≡ (mren η ∘ msub ξ) 𝒟                    comp-mren-msub
                 msubs₁ (mrens₁ η ξ) ψ ≡ (mrens₁ η ∘ msubs₁ ξ) ψ                comp-mrens₁-msubs₁
        msubs₁ (mlifts₁ ξ) (mlifts₁ ψ) ≡ (mlifts₁ ∘ msubs₁ ξ) ψ                 comp-mlifts₁-msubs₁

                          msub mids₁ 𝒟 ≡ 𝒟                                      id-msub
                   msub (msubs₁ ξ ψ) 𝒟 ≡ (msub ξ ∘ msub ψ) 𝒟                    comp-msub
                         msubs mids₁ ξ ≡ ξ                                      -- lid-msubs
                        msubs₁ mids₁ ξ ≡ ξ                                      lid-msubs₁
                        msubs₁ ξ mids₁ ≡ ξ                                      rid-msubs₁
                 msubs₁ (msubs₁ ξ ψ) φ ≡ msubs₁ ξ (msubs₁ ψ φ)                  assoc-msubs₁
-}
--------------------------------------------------------------------------------


comp-msub-mren : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⊢⋆₁ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⨾ Γ ⊢ A true)
                                → msub (gets ξ η) 𝒟 ≡ (msub ξ ∘ mren η) 𝒟
comp-msub-mren ξ η (var 𝒾)      = refl
comp-msub-mren ξ η (lam 𝒟)      = lam & comp-msub-mren ξ η 𝒟
comp-msub-mren ξ η (app 𝒟 ℰ)    = app & comp-msub-mren ξ η 𝒟 ⊗ comp-msub-mren ξ η ℰ
comp-msub-mren ξ η (mvar 𝒾)     = sub ∙ & comp-get-ren∋ ξ η 𝒾
comp-msub-mren ξ η (box 𝒟)      = box & comp-msub-mren ξ η 𝒟
comp-msub-mren ξ η (letbox 𝒟 ℰ) = letbox & comp-msub-mren ξ η 𝒟
                                         ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts₁-gets ξ η ⁻¹
                                           ⋮ comp-msub-mren (mlifts₁ ξ) (keep η) ℰ
                                           )


--------------------------------------------------------------------------------


-- TODO: Better name?

expand-msubs₁ : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ) (𝒟 : Δ ⊢₁ A valid)
                            → msubs₁ (ξ , 𝒟) (mwks₁ ψ) ≡ msubs₁ ξ ψ
expand-msubs₁ ξ ∙       𝒟 = refl
expand-msubs₁ ξ (ψ , ℰ) 𝒟 = _,_ & expand-msubs₁ ξ ψ 𝒟
                                ⊗ ( comp-msub-mren (ξ , 𝒟) (drop id⊇) ℰ ⁻¹
                                  ⋮ (\ ξ′ → msub ξ′ ℰ) & id-gets ξ
                                  )


--------------------------------------------------------------------------------


comp-mren-msub : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ) (𝒟 : Ξ ⨾ Γ ⊢ A true)
                                → msub (mrens₁ η ξ) 𝒟 ≡ (mren η ∘ msub ξ) 𝒟
comp-mren-msub η ξ (var 𝒾)      = refl
comp-mren-msub η ξ (lam 𝒟)      = lam & comp-mren-msub η ξ 𝒟
comp-mren-msub η ξ (app 𝒟 ℰ)    = app & comp-mren-msub η ξ 𝒟 ⊗ comp-mren-msub η ξ ℰ
comp-mren-msub η ξ (mvar 𝒾)     = sub ∙ & comp-mren-get₁ η ξ 𝒾
                                ⋮ comp-mren-sub η ∙ (get ξ 𝒾)
comp-mren-msub η ξ (box 𝒟)      = box & comp-mren-msub η ξ 𝒟
comp-mren-msub η ξ (letbox 𝒟 ℰ) = letbox & comp-mren-msub η ξ 𝒟
                                         ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts₁-mrens₁ η ξ ⁻¹
                                           ⋮ comp-mren-msub (keep η) (mlifts₁ ξ) ℰ
                                           )


comp-mrens₁-msubs₁ : ∀ {Δ Δ′ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ)
                                  → msubs₁ (mrens₁ η ξ) ψ ≡ (mrens₁ η ∘ msubs₁ ξ) ψ
comp-mrens₁-msubs₁ η ξ ∙       = refl
comp-mrens₁-msubs₁ η ξ (ψ , 𝒟) = _,_ & comp-mrens₁-msubs₁ η ξ ψ ⊗ comp-mren-msub η ξ 𝒟


comp-mlifts₁-msubs₁ : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ)
                                  → msubs₁ (mlifts₁ {A} ξ) (mlifts₁ ψ) ≡ (mlifts₁ ∘ msubs₁ ξ) ψ
comp-mlifts₁-msubs₁ ξ ψ = (_, mvz) & ( expand-msubs₁ (mwks₁ ξ) ψ mvz
                                     ⋮ comp-mrens₁-msubs₁ (drop id⊇) ξ ψ
                                     )


--------------------------------------------------------------------------------


id-msub : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                    → msub mids₁ 𝒟 ≡ 𝒟
id-msub (var 𝒾)      = refl
id-msub (lam 𝒟)      = lam & id-msub 𝒟
id-msub (app 𝒟 ℰ)    = app & id-msub 𝒟 ⊗ id-msub ℰ
id-msub (mvar 𝒾)     = sub ∙ & mvar-id-get₁ 𝒾
id-msub (box 𝒟)      = box & id-msub 𝒟
id-msub (letbox 𝒟 ℰ) = letbox & id-msub 𝒟 ⊗ id-msub ℰ


comp-sub-msub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⨾ Γ ⊢⋆ Ψ) (𝒟 : Ξ ⨾ Ψ ⊢ A true)
                              → msub {Γ = Γ} ξ (sub ψ 𝒟) ≡ sub (msubs ξ ψ) (msub ξ 𝒟)
comp-sub-msub ξ ψ (var 𝒾)      = {!!}
comp-sub-msub ξ ψ (lam 𝒟)      = lam & {!( (\ ξ′ → msub ξ′ 𝒟) & ? ⁻¹
                                       ⋮ comp-sub-msub ? ? 𝒟
                                       )!}
comp-sub-msub ξ ψ (app 𝒟 ℰ)    = app & comp-sub-msub ξ ψ 𝒟 ⊗ comp-sub-msub ξ ψ ℰ
comp-sub-msub ξ ψ (mvar 𝒾)     = {!!}
comp-sub-msub ξ ψ (box 𝒟)      = refl
comp-sub-msub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-sub-msub ξ ψ 𝒟
                                        ⊗ {!!}


comp-sub₀-msub : ∀ {Δ Γ Ξ A} → (ξ : Δ ⊢⋆₁ Ξ) (𝒟 : Ξ ⨾ ∙ ⊢ A true)
                             → msub {Γ = Γ} ξ (sub ∙ 𝒟) ≡ sub ∙ (msub ξ 𝒟)
comp-sub₀-msub ξ 𝒟 = comp-sub-msub ξ ∙ 𝒟
-- comp-sub₀-msub ξ (var ())
-- comp-sub₀-msub ξ (lam 𝒟)      = lam & {!comp-sub₀-msub ξ 𝒟!}
-- comp-sub₀-msub ξ (app 𝒟 ℰ)    = app & comp-sub₀-msub ξ 𝒟 ⊗ comp-sub₀-msub ξ ℰ
-- comp-sub₀-msub ξ (mvar 𝒾)     = {!sub ∙ & ?!}
-- comp-sub₀-msub ξ (box 𝒟)      = refl
-- comp-sub₀-msub ξ (letbox 𝒟 ℰ) = letbox & comp-sub₀-msub ξ 𝒟
--                                        ⊗ {!!}


comp-msub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ) (𝒟 : Ψ ⨾ Γ ⊢ A true)
                          → msub (msubs₁ ξ ψ) 𝒟 ≡ (msub ξ ∘ msub ψ) 𝒟
comp-msub ξ ψ (var 𝒾)      = refl
comp-msub ξ ψ (lam 𝒟)      = lam & comp-msub ξ ψ 𝒟
comp-msub ξ ψ (app 𝒟 ℰ)    = app & comp-msub ξ ψ 𝒟 ⊗ comp-msub ξ ψ ℰ
comp-msub ξ ψ (mvar 𝒾)     = sub ∙ & (comp-msub-get ξ ψ 𝒾)
                           ⋮ comp-sub₀-msub ξ (get ψ 𝒾) ⁻¹
comp-msub ξ ψ (box 𝒟)      = box & comp-msub ξ ψ 𝒟
comp-msub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-msub ξ ψ 𝒟
                                    ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts₁-msubs₁ ξ ψ ⁻¹
                                      ⋮ comp-msub (mlifts₁ ξ) (mlifts₁ ψ) ℰ
                                      )


-- NOTE: Unused.

-- lid-msubs : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
--                       → msubs mids₁ ξ ≡ ξ
-- lid-msubs ∙       = refl
-- lid-msubs (ξ , 𝒟) = _,_ & lid-msubs ξ ⊗ id-msub 𝒟


lid-msubs₁ : ∀ {Δ Ξ} → (ξ : Δ ⊢⋆₁ Ξ)
                     → msubs₁ mids₁ ξ ≡ ξ
lid-msubs₁ ∙       = refl
lid-msubs₁ (ξ , 𝒟) = _,_ & lid-msubs₁ ξ ⊗ id-msub 𝒟


rid-msubs₁ : ∀ {Δ Ξ} → (ξ : Δ ⊢⋆₁ Ξ)
                     → msubs₁ ξ mids₁ ≡ ξ
rid-msubs₁ ∙       = refl
rid-msubs₁ (ξ , 𝒟) = _,_ & ( expand-msubs₁ ξ mids₁ 𝒟
                           ⋮ rid-msubs₁ ξ
                           )
                         ⊗ id-sub 𝒟 -- sub ∙ 𝒟 ≡ 𝒟


assoc-msubs₁ : ∀ {Δ Ξ Ψ Φ} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ) (φ : Ψ ⊢⋆₁ Φ)
                           → msubs₁ (msubs₁ ξ ψ) φ ≡ msubs₁ ξ (msubs₁ ψ φ)
assoc-msubs₁ ξ ψ ∙       = refl
assoc-msubs₁ ξ ψ (φ , 𝒟) = _,_ & assoc-msubs₁ ξ ψ φ ⊗ comp-msub ξ ψ 𝒟


instance
  S4₁ : Category (List Validity) _⊢⋆₁_
  S4₁ = record
          { id     = mids₁
          ; _∘_    = flip msubs₁
          ; lid∘   = rid-msubs₁
          ; rid∘   = lid-msubs₁
          ; assoc∘ = \ ξ₁ ξ₂ ξ₃ → assoc-msubs₁ ξ₃ ξ₂ ξ₁ ⁻¹
          }


Msub : ∀ {A} → Presheaf (_⊢₁ A valid) msub
Msub = record
         { idℱ   = funext! id-msub
         ; compℱ = \ ξ₁ ξ₂ → funext! (comp-msub ξ₂ ξ₁)
         }


--------------------------------------------------------------------------------
