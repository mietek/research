module StdS4Lemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open GetAllList
open import AllListLemmas
open GetsAllList
open import StdS4


--------------------------------------------------------------------------------
{-
                             ren id⊇ 𝒟 ≡ 𝒟                                      id-ren
                      ren (η₁ ∘⊇ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟                    comp-ren
                        ren (drop η) 𝒟 ≡ (wk ∘ ren η) 𝒟                         -- comp-wk-ren-drop
                 (ren (keep η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟                         comp-wk-ren-keep

                            mren id⊇ 𝒟 ≡ 𝒟                                      id-mren
                     mren (η₁ ∘⊇ η₂) 𝒟 ≡ (mren η₂ ∘ mren η₁) 𝒟                  comp-mren
                       mren (drop η) 𝒟 ≡ (mwk ∘ mren η) 𝒟                       comp-mwk-mren-drop
               (mren (keep η) ∘ mwk) 𝒟 ≡ (mwk ∘ mren η) 𝒟                       comp-mwk-mren-keep

                  (mren η₁ ∘ ren η₂) 𝒟 ≡ (ren η₂ ∘ mren η₁) 𝒟                   comp-ren-mren
                (mrens η₁ ∘ rens η₂) ξ ≡ (rens η₂ ∘ mrens η₁) ξ                 comp-rens-mrens
                   (mrens η ∘ lifts) ξ ≡ (lifts ∘ mrens η) ξ                    comp-lifts-mrens

                  (ren η₂ ∘ mren η₁) 𝒟 ≡ (mren η₁ ∘ ren η₂) 𝒟                   comp-mren-ren
                (rens η₂ ∘ mrens η₁) ξ ≡ (mrens η₁ ∘ rens η₂) ξ                 comp-mrens-rens
                   (lifts ∘ mrens η) ξ ≡ (mrens η ∘ lifts {A}) ξ                comp-mrens-lifts

                            rens id⊇ ξ ≡ ξ                                      id-rens
                     rens (η₁ ∘⊇ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ                  comp-rens
                       rens (drop η) ξ ≡ (wks ∘ rens η) ξ                       -- comp-wks-rens-drop
               (rens (keep η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ                       comp-wks-rens-keep
             (rens (keep η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ                     comp-lifts-rens

                           mrens id⊇ ξ ≡ ξ                                      id-mrens
                    mrens (η₁ ∘⊇ η₂) ξ ≡ (mrens η₂ ∘ mrens η₁) ξ                comp-mrens
                      mrens (drop η) ξ ≡ (mwks ∘ mrens η) ξ                     comp-mwks-mrens-drop
             (mrens (keep η) ∘ mwks) ξ ≡ (mwks ∘ mrens η) ξ                     comp-mwks-mrens-keep

                          mrens₁ id⊇ ξ ≡ ξ                                      id-mrens₁
                   mrens₁ (η₁ ∘⊇ η₂) ξ ≡ (mrens₁ η₂ ∘ mrens₁ η₁) ξ              comp-mrens₁
                     mrens₁ (drop η) ξ ≡ (mwks₁ ∘ mrens₁ η) ξ                   comp-mwks₁-mrens₁-drop
           (mrens₁ (keep η) ∘ mwks₁) ξ ≡ (mwks₁ ∘ mrens₁ η) ξ                   comp-mwks₁-mrens₁-keep
         (mrens₁ (keep η) ∘ mlifts₁) ξ ≡ (mlifts₁ ∘ mrens₁ η) ξ                 comp-mlifts₁-mrens₁

                      get (rens η ξ) 𝒾 ≡ (ren η ∘ get ξ) 𝒾                      comp-ren-get
                             get ids 𝒾 ≡ var 𝒾                                  var-id-get

                     get (mrens η ξ) 𝒾 ≡ (mren η ∘ get ξ) 𝒾                     comp-mren-get

                    get (mrens₁ η ξ) 𝒾 ≡ (mren η ∘ get ξ) 𝒾                     comp-mren-get₁
                           get mids₁ 𝒾 ≡ mvar 𝒾                                 mvar-id-get₁

                   gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂                  comp-rens-gets
               gets (lifts ξ) (keep η) ≡ (lifts ∘ gets ξ) η                     comp-lifts-gets

                  gets (mrens η₁ ξ) η₂ ≡ (mrens η₁ ∘ gets ξ) η₂                 comp-mrens-gets

                 gets (mrens₁ η₁ ξ) η₂ ≡ (mrens₁ η₁ ∘ gets ξ) η₂                comp-mrens₁-gets
             gets (mlifts₁ ξ) (keep η) ≡ (mlifts₁ ∘ gets ξ) η                   comp-mlifts₁-gets

                      get (subs ξ ψ) 𝒾 ≡ (sub ξ ∘ get ψ) 𝒾                      comp-sub-get
                     gets (subs ξ ψ) η ≡ (subs ξ ∘ gets ψ) η                    -- comp-subs-gets

                     get (msubs ξ ψ) 𝒾 ≡ (msub ξ ∘ get ψ) 𝒾                     comp-msub-get
                    gets (msubs ξ ψ) η ≡ (msubs ξ ∘ gets ψ) η                   -- comp-msubs-gets

                      sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟                      comp-sub-ren
                     subs (gets ξ η) ψ ≡ (subs ξ ∘ rens η) ψ                    -- comp-subs-rens

                  subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ                               expand-subs

                      sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟                      comp-ren-sub
                     subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ                    comp-rens-subs
              subs (lifts ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ                     comp-lifts-subs

                   sub (mrens η ids) 𝒟 ≡ 𝒟                                      id-mren-sub
            sub (mrens η ξ) (mren η 𝒟) ≡ (mren η ∘ sub ξ) 𝒟                     comp-mren-sub
          subs (mrens η ξ) (mrens η ψ) ≡ (mrens η ∘ subs ξ) ψ                   comp-mrens-subs

                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                      sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟                      comp-sub
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs


-}
--------------------------------------------------------------------------------


id-ren : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                   → ren id⊇ 𝒟 ≡ 𝒟
id-ren (var 𝒾)      = var & id-ren∋ 𝒾
id-ren (lam 𝒟)      = lam & id-ren 𝒟
id-ren (app 𝒟 ℰ)    = app & id-ren 𝒟 ⊗ id-ren ℰ
id-ren (mvar 𝒾)     = refl
id-ren (box 𝒟)      = refl
id-ren (letbox 𝒟 ℰ) = letbox & id-ren 𝒟 ⊗ id-ren ℰ


comp-ren : ∀ {Δ Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Δ ⨾ Γ ⊢ A true)
                           → ren (η₁ ∘⊇ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟
comp-ren η₁ η₂ (var 𝒾)      = var & comp-ren∋ η₁ η₂ 𝒾
comp-ren η₁ η₂ (lam 𝒟)      = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ)    = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ
comp-ren η₁ η₂ (mvar 𝒾)     = refl
comp-ren η₁ η₂ (box 𝒟)      = refl
comp-ren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ


Ren : ∀ {A} → Presheaf (\ Γ → Σ (List Validity) (\ Δ → Δ ⨾ Γ ⊢ A true))
                        (\ { η (Δ , 𝒟) → Δ , ren η 𝒟 })
Ren = record
        { idℱ   = funext! (\ { (Δ , 𝒟) → (Δ ,_) & id-ren 𝒟 })
        ; compℱ = \ η₁ η₂ → funext! (\ { (Δ , 𝒟) → (Δ ,_) & comp-ren η₁ η₂ 𝒟 })
        }


-- NOTE: Unused.

-- comp-wk-ren-drop : ∀ {Δ Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Δ ⨾ Γ ⊢ A true)
--                                   → ren (drop {A = B} η) 𝒟 ≡ (wk ∘ ren η) 𝒟
-- comp-wk-ren-drop η 𝒟 = (\ η′ → ren (drop η′) 𝒟) & rid∘⊇ η ⁻¹
--                      ⋮ comp-ren η (drop id⊇) 𝒟


comp-wk-ren-keep : ∀ {Δ Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                  → (ren (keep {A = B} η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟
comp-wk-ren-keep η 𝒟 = comp-ren (drop id⊇) (keep η) 𝒟 ⁻¹
                     ⋮ (\ η′ → ren (drop η′) 𝒟) & (lid∘⊇ η ⋮ rid∘⊇ η ⁻¹)
                     ⋮ comp-ren η (drop id⊇) 𝒟


--------------------------------------------------------------------------------


id-mren : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                    → mren id⊇ 𝒟 ≡ 𝒟
id-mren (var 𝒾)      = refl
id-mren (lam 𝒟)      = lam & id-mren 𝒟
id-mren (app 𝒟 ℰ)    = app & id-mren 𝒟 ⊗ id-mren ℰ
id-mren (mvar 𝒾)     = mvar & id-ren∋ 𝒾
id-mren (box 𝒟)      = box & id-mren 𝒟
id-mren (letbox 𝒟 ℰ) = letbox & id-mren 𝒟 ⊗ id-mren ℰ


comp-mren : ∀ {Δ Δ′ Δ″ Γ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (𝒟 : Δ ⨾ Γ ⊢ A true)
                            → mren (η₁ ∘⊇ η₂) 𝒟 ≡ (mren η₂ ∘ mren η₁) 𝒟
comp-mren η₁ η₂ (var 𝒾)      = refl
comp-mren η₁ η₂ (lam 𝒟)      = lam & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (app 𝒟 ℰ)    = app & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren η₁ η₂ ℰ
comp-mren η₁ η₂ (mvar 𝒾)     = mvar & comp-ren∋ η₁ η₂ 𝒾
comp-mren η₁ η₂ (box 𝒟)      = box & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren (keep η₁) (keep η₂) ℰ


Mren : ∀ {A} → Presheaf (\ Δ → Σ (List Truth) (\ Γ → Δ ⨾ Γ ⊢ A true))
                         (\ { η (Γ , 𝒟) → Γ , mren η 𝒟 })
Mren = record
         { idℱ   = funext! (\ { (Γ , 𝒟) → (Γ ,_) & id-mren 𝒟 })
         ; compℱ = \ η₁ η₂ → funext! (\ { (Γ , 𝒟) → (Γ ,_) & comp-mren η₁ η₂ 𝒟 })
         }


comp-mwk-mren-drop : ∀ {Δ Δ′ Γ A B} → (η : Δ′ ⊇ Δ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                    → mren (drop {A = B} η) 𝒟 ≡ (mwk ∘ mren η) 𝒟
comp-mwk-mren-drop η 𝒟 = (\ η′ → mren (drop η′) 𝒟) & rid∘⊇ η ⁻¹
                       ⋮ comp-mren η (drop id⊇) 𝒟


comp-mwk-mren-keep : ∀ {Δ Δ′ Γ A B} → (η : Δ′ ⊇ Δ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                    → (mren (keep {A = B} η) ∘ mwk) 𝒟 ≡ (mwk ∘ mren η) 𝒟
comp-mwk-mren-keep η 𝒟 = comp-mren (drop id⊇) (keep η) 𝒟 ⁻¹
                       ⋮ (\ η′ → mren (drop η′) 𝒟) & (lid∘⊇ η ⋮ rid∘⊇ η ⁻¹)
                       ⋮ comp-mren η (drop id⊇) 𝒟


--------------------------------------------------------------------------------


comp-ren-mren : ∀ {Δ Δ′ Γ Γ′ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                → (mren η₁ ∘ ren η₂) 𝒟 ≡ (ren η₂ ∘ mren η₁) 𝒟
comp-ren-mren η₁ η₂ (var 𝒾)      = refl
comp-ren-mren η₁ η₂ (lam 𝒟)      = lam & comp-ren-mren η₁ (keep η₂) 𝒟
comp-ren-mren η₁ η₂ (app 𝒟 ℰ)    = app & comp-ren-mren η₁ η₂ 𝒟 ⊗ comp-ren-mren η₁ η₂ ℰ
comp-ren-mren η₁ η₂ (mvar 𝒾)     = refl
comp-ren-mren η₁ η₂ (box 𝒟)      = refl
comp-ren-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-ren-mren η₁ η₂ 𝒟 ⊗ comp-ren-mren (keep η₁) η₂ ℰ


comp-rens-mrens : ∀ {Δ Δ′ Γ Γ′ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                  → (mrens η₁ ∘ rens η₂) ξ ≡ (rens η₂ ∘ mrens η₁) ξ
comp-rens-mrens η₁ η₂ ∙       = refl
comp-rens-mrens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens-mrens η₁ η₂ ξ ⊗ comp-ren-mren η₁ η₂ 𝒟


comp-lifts-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                  → (mrens η ∘ lifts {A}) ξ ≡ (lifts ∘ mrens η) ξ
comp-lifts-mrens η ξ = (_, vz) & comp-rens-mrens η (drop id⊇) ξ


--------------------------------------------------------------------------------


comp-mren-ren : ∀ {Δ Δ′ Γ Γ′ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                → (ren η₂ ∘ mren η₁) 𝒟 ≡ (mren η₁ ∘ ren η₂) 𝒟
comp-mren-ren η₁ η₂ 𝒟 = comp-ren-mren η₁ η₂ 𝒟 ⁻¹
-- comp-mren-ren η₁ η₂ (var 𝒾)      = refl
-- comp-mren-ren η₁ η₂ (lam 𝒟)      = lam & comp-mren-ren η₁ (keep η₂) 𝒟
-- comp-mren-ren η₁ η₂ (app 𝒟 ℰ)    = app & comp-mren-ren η₁ η₂ 𝒟 ⊗ comp-mren-ren η₁ η₂ ℰ
-- comp-mren-ren η₁ η₂ (mvar 𝒾)     = refl
-- comp-mren-ren η₁ η₂ (box 𝒟)      = refl
-- comp-mren-ren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-mren-ren η₁ η₂ 𝒟 ⊗ comp-mren-ren (keep η₁) η₂ ℰ


comp-mrens-rens : ∀ {Δ Δ′ Γ Γ′ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                  → (rens η₂ ∘ mrens η₁) ξ ≡ (mrens η₁ ∘ rens η₂) ξ
comp-mrens-rens η₁ η₂ ξ = comp-rens-mrens η₁ η₂ ξ ⁻¹
-- comp-mrens-rens η₁ η₂ ∙       = refl
-- comp-mrens-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens-rens η₁ η₂ ξ ⊗ comp-mren-ren η₁ η₂ 𝒟


-- NOTE: Unused.

-- comp-mrens-lifts : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
--                                   → (lifts ∘ mrens η) ξ ≡ (mrens η ∘ lifts {A}) ξ
-- comp-mrens-lifts η ξ = comp-lifts-mrens η ξ ⁻¹
-- -- comp-mrens-lifts η ξ = (_, vz) & comp-mrens-rens η (drop id⊇) ξ


--------------------------------------------------------------------------------


id-rens : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                    → rens id⊇ ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟


comp-rens : ∀ {Δ Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                            → rens (η₁ ∘⊇ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟


Rens : ∀ {Ξ} → Presheaf (\ Γ → Σ (List Validity) (\ Δ → Δ ⨾ Γ ⊢⋆ Ξ))
                         (\ { η (Δ , ξ) → Δ , rens η ξ })
Rens = record
         { idℱ   = funext! (\ { (Δ , ξ) → (Δ ,_) & id-rens ξ })
         ; compℱ = \ η₁ η₂ → funext! (\ { (Δ , ξ) → (Δ ,_) & comp-rens η₁ η₂ ξ })
         }


-- NOTE: Unused.

-- comp-wks-rens-drop : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
--                                     → rens (drop {A = A} η) ξ ≡ (wks ∘ rens η) ξ
-- comp-wks-rens-drop η ∙       = refl
-- comp-wks-rens-drop η (ξ , 𝒟) = _,_ & comp-wks-rens-drop η ξ ⊗ comp-wk-ren-drop η 𝒟


comp-wks-rens-keep : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                    → (rens (keep {A = A} η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ
comp-wks-rens-keep η ∙       = refl
comp-wks-rens-keep η (ξ , 𝒟) = _,_ & comp-wks-rens-keep η ξ ⊗ comp-wk-ren-keep η 𝒟


comp-lifts-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                 → (rens (keep {A = A} η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ
comp-lifts-rens η ξ = (_, vz) & comp-wks-rens-keep η ξ


--------------------------------------------------------------------------------


id-mrens : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → mrens id⊇ ξ ≡ ξ
id-mrens ∙       = refl
id-mrens (ξ , 𝒟) = _,_ & id-mrens ξ ⊗ id-mren 𝒟


comp-mrens : ∀ {Δ Δ′ Δ″ Γ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → mrens (η₁ ∘⊇ η₂) ξ ≡ (mrens η₂ ∘ mrens η₁) ξ
comp-mrens η₁ η₂ ∙       = refl
comp-mrens η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens η₁ η₂ ξ ⊗ comp-mren η₁ η₂ 𝒟


Mrens : ∀ {Ξ} → Presheaf (\ Δ → Σ (List Truth) (\ Γ → Δ ⨾ Γ ⊢⋆ Ξ))
                          (\ { η (Γ , ξ) → Γ , mrens η ξ})
Mrens = record
          { idℱ   = funext! (\ { (Γ , ξ) → (Γ ,_) & id-mrens ξ })
          ; compℱ = \ η₁ η₂ → funext! (\ { (Γ , ξ) → (Γ ,_) & comp-mrens η₁ η₂ ξ })
          }


comp-mwks-mrens-drop : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                      → mrens (drop {A = A} η) ξ ≡ (mwks ∘ mrens η) ξ
comp-mwks-mrens-drop η ∙       = refl
comp-mwks-mrens-drop η (ξ , 𝒟) = _,_ & comp-mwks-mrens-drop η ξ ⊗ comp-mwk-mren-drop η 𝒟


comp-mwks-mrens-keep : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                      → (mrens (keep {A = A} η) ∘ mwks) ξ ≡ (mwks ∘ mrens η) ξ
comp-mwks-mrens-keep η ∙       = refl
comp-mwks-mrens-keep η (ξ , 𝒟) = _,_ & comp-mwks-mrens-keep η ξ ⊗ comp-mwk-mren-keep η 𝒟


--------------------------------------------------------------------------------


id-mrens₁ : ∀ {Δ Ξ} → (ξ : Δ ⊢⋆₁ Ξ)
                    → mrens₁ id⊇ ξ ≡ ξ
id-mrens₁ ∙       = refl
id-mrens₁ (ξ , 𝒟) = _,_ & id-mrens₁ ξ ⊗ id-mren 𝒟


comp-mrens₁ : ∀ {Δ Δ′ Δ″ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (ξ : Δ ⊢⋆₁ Ξ)
                            → mrens₁ (η₁ ∘⊇ η₂) ξ ≡ (mrens₁ η₂ ∘ mrens₁ η₁) ξ
comp-mrens₁ η₁ η₂ ∙       = refl
comp-mrens₁ η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens₁ η₁ η₂ ξ ⊗ comp-mren η₁ η₂ 𝒟


Mrens₁ : ∀ {Ξ} → Presheaf (_⊢⋆₁ Ξ) mrens₁
Mrens₁ = record
           { idℱ   = funext! id-mrens₁
           ; compℱ = \ η₁ η₂ → funext! (comp-mrens₁ η₁ η₂)
           }


comp-mwks₁-mrens₁-drop : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                      → mrens₁ (drop {A = A} η) ξ ≡ (mwks₁ ∘ mrens₁ η) ξ
comp-mwks₁-mrens₁-drop η ∙       = refl
comp-mwks₁-mrens₁-drop η (ξ , 𝒟) = _,_ & comp-mwks₁-mrens₁-drop η ξ ⊗ comp-mwk-mren-drop η 𝒟


comp-mwks₁-mrens₁-keep : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                      → (mrens₁ (keep {A = A} η) ∘ mwks₁) ξ ≡ (mwks₁ ∘ mrens₁ η) ξ
comp-mwks₁-mrens₁-keep η ∙       = refl
comp-mwks₁-mrens₁-keep η (ξ , 𝒟) = _,_ & comp-mwks₁-mrens₁-keep η ξ ⊗ comp-mwk-mren-keep η 𝒟


comp-mlifts₁-mrens₁ : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                   → (mrens₁ (keep {A = A} η) ∘ mlifts₁) ξ ≡ (mlifts₁ ∘ mrens₁ η) ξ
comp-mlifts₁-mrens₁ η ξ = (_, mvz) & comp-mwks₁-mrens₁-keep η ξ


--------------------------------------------------------------------------------


comp-ren-get : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                              → get (rens η ξ) 𝒾 ≡ (ren η ∘ get ξ) 𝒾
comp-ren-get η (ξ , 𝒟) zero    = refl
comp-ren-get η (ξ , 𝒟) (suc 𝒾) = comp-ren-get η ξ 𝒾


var-id-get : ∀ {Δ Γ A} → (𝒾 : Γ ∋ A true)
                       → get (ids {Δ = Δ}) 𝒾 ≡ var 𝒾
var-id-get zero    = refl
var-id-get (suc 𝒾) = comp-ren-get (drop id⊇) ids 𝒾
                   ⋮ wk & var-id-get 𝒾
                   ⋮ (\ 𝒾′ → var (suc 𝒾′)) & id-ren∋ 𝒾


--------------------------------------------------------------------------------


comp-mren-get : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                               → get (mrens η ξ) 𝒾 ≡ (mren η ∘ get ξ) 𝒾
comp-mren-get η (ξ , 𝒟) zero    = refl
comp-mren-get η (ξ , 𝒟) (suc 𝒾) = comp-mren-get η ξ 𝒾


--------------------------------------------------------------------------------


comp-mren-get₁ : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ) (𝒾 : Ξ ∋ A valid)
                              → get (mrens₁ η ξ) 𝒾 ≡ (mren η ∘ get ξ) 𝒾
comp-mren-get₁ η (ξ , 𝒟) zero    = refl
comp-mren-get₁ η (ξ , 𝒟) (suc 𝒾) = comp-mren-get₁ η ξ 𝒾


mvar-id-get₁ : ∀ {Δ A} → (𝒾 : Δ ∋ A valid)
                       → get mids₁ 𝒾 ≡ mvar 𝒾
mvar-id-get₁ zero    = refl
mvar-id-get₁ (suc 𝒾) = comp-mren-get₁ (drop id⊇) mids₁ 𝒾
                     ⋮ mwk & mvar-id-get₁ 𝒾
                     ⋮ (\ 𝒾′ → mvar (suc 𝒾′)) & id-ren∋ 𝒾


--------------------------------------------------------------------------------


comp-rens-gets : ∀ {Δ Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                                 → gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂
comp-rens-gets η₁ ∙       done      = refl
comp-rens-gets η₁ (ξ , 𝒟) (drop η₂) = comp-rens-gets η₁ ξ η₂
comp-rens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & comp-rens-gets η₁ ξ η₂


comp-lifts-gets : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                                 → gets (lifts {A} ξ) (keep η) ≡ (lifts ∘ gets ξ) η
comp-lifts-gets ξ η = (_, vz) & comp-rens-gets (drop id⊇) ξ η


--------------------------------------------------------------------------------


comp-mrens-gets : ∀ {Δ Δ′ Γ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                                  → gets (mrens η₁ ξ) η₂ ≡ (mrens η₁ ∘ gets ξ) η₂
comp-mrens-gets η₁ ∙       done      = refl
comp-mrens-gets η₁ (ξ , 𝒟) (drop η₂) = comp-mrens-gets η₁ ξ η₂
comp-mrens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & comp-mrens-gets η₁ ξ η₂


--------------------------------------------------------------------------------


comp-mrens₁-gets : ∀ {Δ Δ′ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                                 → gets (mrens₁ η₁ ξ) η₂ ≡ (mrens₁ η₁ ∘ gets ξ) η₂
comp-mrens₁-gets η₁ ∙       done      = refl
comp-mrens₁-gets η₁ (ξ , 𝒟) (drop η₂) = comp-mrens₁-gets η₁ ξ η₂
comp-mrens₁-gets η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & comp-mrens₁-gets η₁ ξ η₂


comp-mlifts₁-gets : ∀ {Δ Ξ Ξ′ A} → (ξ : Δ ⊢⋆₁ Ξ′) (η : Ξ′ ⊇ Ξ)
                                 → gets (mlifts₁ {A} ξ) (keep η) ≡ (mlifts₁ ∘ gets ξ) η
comp-mlifts₁-gets ξ η = (_, mvz) & comp-mrens₁-gets (drop id⊇) ξ η


--------------------------------------------------------------------------------


comp-sub-get : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                             → get (subs ξ ψ) 𝒾 ≡ (sub ξ ∘ get ψ) 𝒾
comp-sub-get ξ (ψ , 𝒟) zero    = refl
comp-sub-get ξ (ψ , ℰ) (suc 𝒾) = comp-sub-get ξ ψ 𝒾


-- NOTE: Unused.

-- comp-subs-gets : ∀ {Δ Γ Ξ Ψ Ψ′} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
--                                 → gets (subs ξ ψ) η ≡ (subs ξ ∘ gets ψ) η
-- comp-subs-gets ξ ∙       done     = refl
-- comp-subs-gets ξ (ψ , 𝒟) (drop η) = comp-subs-gets ξ ψ η
-- comp-subs-gets ξ (ψ , 𝒟) (keep η) = (_, sub ξ 𝒟) & comp-subs-gets ξ ψ η


--------------------------------------------------------------------------------


comp-msub-get : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ) (𝒾 : Ψ ∋ A valid)
                            → get (msubs₁ ξ ψ) 𝒾 ≡ (msub ξ ∘ get ψ) 𝒾
comp-msub-get ξ (ψ , 𝒟) zero    = refl
comp-msub-get ξ (ψ , ℰ) (suc 𝒾) = comp-msub-get ξ ψ 𝒾


-- NOTE: Unused.

-- comp-msubs-gets : ∀ {Δ Ξ Ψ Ψ′} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ′) (η : Ψ′ ⊇ Ψ)
--                                → gets (msubs₁ ξ ψ) η ≡ (msubs₁ ξ ∘ gets ψ) η
-- comp-msubs-gets ξ ∙       done     = refl
-- comp-msubs-gets ξ (ψ , 𝒟) (drop η) = comp-msubs-gets ξ ψ η
-- comp-msubs-gets ξ (ψ , 𝒟) (keep η) = (_, msub ξ 𝒟) & comp-msubs-gets ξ ψ η


--------------------------------------------------------------------------------


comp-sub-ren : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                              → sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟
comp-sub-ren ξ η (var 𝒾)      = comp-get-ren∋ ξ η 𝒾
comp-sub-ren ξ η (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-gets ξ η ⁻¹
                                      ⋮ comp-sub-ren (lifts ξ) (keep η) 𝒟
                                      )
comp-sub-ren ξ η (app 𝒟 ℰ)    = app & comp-sub-ren ξ η 𝒟 ⊗ comp-sub-ren ξ η ℰ
comp-sub-ren ξ η (mvar 𝒾)     = refl
comp-sub-ren ξ η (box 𝒟)      = refl
comp-sub-ren ξ η (letbox 𝒟 ℰ) = letbox & comp-sub-ren ξ η 𝒟
                                       ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mrens-gets (drop id⊇) ξ η ⁻¹
                                         ⋮ comp-sub-ren (mwks ξ) η ℰ
                                         )


-- NOTE: Unused.

-- comp-subs-rens : ∀ {Δ Γ Ξ Ξ′ Ψ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
--                                 → subs (gets ξ η) ψ ≡ (subs ξ ∘ rens η) ψ
-- comp-subs-rens ξ η ∙       = refl
-- comp-subs-rens ξ η (ψ , 𝒟) = _,_ & comp-subs-rens ξ η ψ ⊗ comp-sub-ren ξ η 𝒟


--------------------------------------------------------------------------------


-- TODO: Better name?

expand-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                            → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
expand-subs ξ ∙       𝒟 = refl
expand-subs ξ (ψ , ℰ) 𝒟 = _,_ & expand-subs ξ ψ 𝒟
                              ⊗ ( comp-sub-ren (ξ , 𝒟) (drop id⊇) ℰ ⁻¹
                                ⋮ (\ ξ′ → sub ξ′ ℰ) & id-gets ξ
                                )


--------------------------------------------------------------------------------


comp-ren-sub : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                              → sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟
comp-ren-sub η ξ (var 𝒾)      = comp-ren-get η ξ 𝒾
comp-ren-sub η ξ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-rens η ξ ⁻¹
                                      ⋮ comp-ren-sub (keep η) (lifts ξ) 𝒟
                                      )
comp-ren-sub η ξ (app 𝒟 ℰ)    = app & comp-ren-sub η ξ 𝒟 ⊗ comp-ren-sub η ξ ℰ
comp-ren-sub η ξ (mvar 𝒾)     = refl
comp-ren-sub η ξ (box 𝒟)      = refl
comp-ren-sub η ξ (letbox 𝒟 ℰ) = letbox & comp-ren-sub η ξ 𝒟
                                       ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mrens-rens (drop id⊇) η ξ ⁻¹
                                         ⋮ comp-ren-sub η (mwks ξ) ℰ
                                         )


comp-rens-subs : ∀ {Δ Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                                → subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ
comp-rens-subs η ξ ∙       = refl
comp-rens-subs η ξ (ψ , 𝒟) = _,_ & comp-rens-subs η ξ ψ ⊗ comp-ren-sub η ξ 𝒟


comp-lifts-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                                → subs (lifts {A} ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ
comp-lifts-subs ξ ψ = (_, vz) & ( expand-subs (wks ξ) ψ vz
                                ⋮ comp-rens-subs (drop id⊇) ξ ψ
                                )


--------------------------------------------------------------------------------


id-mren-sub : ∀ {Δ Δ′ Γ A} → (η : Δ′ ⊇ Δ) (𝒟 : Δ′ ⨾ Γ ⊢ A true)
                           → sub (mrens η ids) 𝒟 ≡ 𝒟
id-mren-sub η (var 𝒾)      = comp-mren-get η ids 𝒾
                           ⋮ mren η & var-id-get 𝒾
id-mren-sub η (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-mrens η ids ⁻¹
                                   ⋮ id-mren-sub η 𝒟
                                   )
id-mren-sub η (app 𝒟 ℰ)    = app & id-mren-sub η 𝒟 ⊗ id-mren-sub η ℰ
id-mren-sub η (mvar 𝒾)     = refl
id-mren-sub η (box 𝒟)      = refl
id-mren-sub η (letbox 𝒟 ℰ) = letbox & id-mren-sub η 𝒟
                                    ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mwks-mrens-drop η ids ⁻¹
                                      ⋮ id-mren-sub (drop η) ℰ
                                      )


comp-mren-sub : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                               → sub (mrens η ξ) (mren η 𝒟) ≡ (mren η ∘ sub ξ) 𝒟
comp-mren-sub η ξ (var 𝒾)      = comp-mren-get η ξ 𝒾
comp-mren-sub η ξ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ (mren η 𝒟)) & comp-lifts-mrens η ξ ⁻¹
                                       ⋮ comp-mren-sub η (lifts ξ) 𝒟
                                       )
comp-mren-sub η ξ (app 𝒟 ℰ)    = app & comp-mren-sub η ξ 𝒟 ⊗ comp-mren-sub η ξ ℰ
comp-mren-sub η ξ (mvar 𝒾)     = refl
comp-mren-sub η ξ (box 𝒟)      = refl
comp-mren-sub η ξ (letbox 𝒟 ℰ) = letbox & comp-mren-sub η ξ 𝒟
                                        ⊗ ( (\ ξ′ → sub ξ′ (mren (keep η) ℰ)) & comp-mwks-mrens-keep η ξ ⁻¹
                                        ⋮ comp-mren-sub (keep η) (mwks ξ) ℰ
                                        )


comp-mrens-subs : ∀ {Δ Δ′ Γ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                                 → subs (mrens η ξ) (mrens η ψ) ≡ (mrens η ∘ subs ξ) ψ
comp-mrens-subs η ξ ∙       = refl
comp-mrens-subs η ξ (ψ , 𝒟) = _,_ & comp-mrens-subs η ξ ψ ⊗ comp-mren-sub η ξ 𝒟


--------------------------------------------------------------------------------


id-sub : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                   → sub ids 𝒟 ≡ 𝒟
id-sub (var 𝒾)      = var-id-get 𝒾
id-sub (lam 𝒟)      = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ)    = app & id-sub 𝒟 ⊗ id-sub ℰ
id-sub (mvar 𝒾)     = refl
id-sub (box 𝒟)      = refl
id-sub (letbox 𝒟 ℰ) = letbox & id-sub 𝒟 ⊗ id-mren-sub (drop id⊇) ℰ


comp-sub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ ⨾ Ψ ⊢ A true)
                         → sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟
comp-sub ξ ψ (var 𝒾)      = comp-sub-get ξ ψ 𝒾
comp-sub ξ ψ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-subs ξ ψ ⁻¹
                                  ⋮ comp-sub (lifts ξ) (lifts ψ) 𝒟
                                  )
comp-sub ξ ψ (app 𝒟 ℰ)    = app & comp-sub ξ ψ 𝒟 ⊗ comp-sub ξ ψ ℰ
comp-sub ξ ψ (mvar 𝒾)     = refl
comp-sub ξ ψ (box 𝒟)      = refl
comp-sub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-sub ξ ψ 𝒟
                                   ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mrens-subs (drop id⊇) ξ ψ ⁻¹
                                     ⋮ comp-sub (mwks ξ) (mwks ψ) ℰ
                                     )


lid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟


rid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( expand-subs ξ ids 𝒟
                            ⋮ rid-subs ξ
                            )


assoc-subs : ∀ {Δ Γ Ξ Ψ Φ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (φ : Δ ⨾ Ψ ⊢⋆ Φ)
                           → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ comp-sub ξ ψ 𝒟


instance
  S4 : ∀ {Δ} → Category (List Truth) (\ Γ Ξ → Δ ⨾ Γ ⊢⋆ Ξ)
  S4 = record
         { id     = ids
         ; _∘_    = flip subs
         ; lid∘   = rid-subs
         ; rid∘   = lid-subs
         ; assoc∘ = \ ξ₁ ξ₂ ξ₃ → assoc-subs ξ₃ ξ₂ ξ₁ ⁻¹
         }


Sub : ∀ {Δ A} → Presheaf {{S4 {Δ}}} (\ Γ → Δ ⨾ Γ ⊢ A true) sub
Sub = record
        { idℱ   = funext! id-sub
        ; compℱ = \ ξ₁ ξ₂ → funext! (comp-sub ξ₂ ξ₁)
        }


--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
