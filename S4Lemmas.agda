module S4Lemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import AllListLemmas
open import S4Propositions
open import S4Derivations


--------------------------------------------------------------------------------
{-
                      get (rens η ξ) i ≡ (ren η ∘ get ξ) i                      comp-ren-get
                   gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂                  comp-rens-gets
             (gets (lifts ξ) ∘ keep) η ≡ (lifts ∘ gets ξ) η                     comp-lifts-gets
                             get ids i ≡ var i                                  get-var

                              ren id 𝒟 ≡ 𝒟                                      id-ren
                             rens id ξ ≡ ξ                                      id-rens
                       ren (η₁ ∘ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟                    comp-ren
                      rens (η₁ ∘ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ                  comp-rens
                                                                                𝐫𝐞𝐧
                                                                                𝐫𝐞𝐧𝐬

                 (ren (keep η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟                         comp-wk-ren-keep
               (rens (keep η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ                       comp-wks-rens-keep
             (rens (keep η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ                     comp-lifts-rens

                  (mren η₁ ∘ ren η₂) 𝒟 ≡ (ren η₂ ∘ mren η₁) 𝒟                   comp-ren-mren
                (mrens η₁ ∘ rens η₂) ξ ≡ (rens η₂ ∘ mrens η₁) ξ                 comp-rens-mrens
                   (mrens η ∘ lifts) ξ ≡ (lifts ∘ mrens η) ξ                    comp-lifts-mrens
                           mrens η ids ≡ ids                                    id-mrens-ids

                     get (mrens η ξ) i ≡ (mren η ∘ get ξ) i                     comp-mren-get
                    get (mrens* η ξ) i ≡ (mren η ∘ get ξ) i                     comp-mren-get*
                  gets (mrens η₁ ξ) η₂ ≡ (mrens η₁ ∘ gets ξ) η₂                 comp-mrens-gets
                 gets (mrens* η₁ ξ) η₂ ≡ (mrens* η₁ ∘ gets ξ) η₂                comp-mrens*-gets
           (gets (mlifts* ξ) ∘ keep) η ≡ (mlifts* ∘ gets ξ) η                   comp-mlifts*-gets
                           get mids* i ≡ mvar i                                 get-mvar

                             mren id 𝒟 ≡ 𝒟                                      id-mren
                            mrens id ξ ≡ ξ                                      id-mrens
                      mren (η₁ ∘ η₂) 𝒟 ≡ (mren η₂ ∘ mren η₁) 𝒟                  comp-mren
                     mrens (η₁ ∘ η₂) ξ ≡ (mrens η₂ ∘ mrens η₁) ξ                comp-mrens
                                                                                𝐦𝐫𝐞𝐧
                                                                                𝐦𝐫𝐞𝐧𝐬

               (mren (keep η) ∘ mwk) 𝒟 ≡ (mwk ∘ mren η) 𝒟                       comp-mwk-mren-keep
             (mrens (keep η) ∘ mwks) ξ ≡ (mwks ∘ mrens η) ξ                     comp-mwks-mrens-keep
           (mrens* (keep η) ∘ mwks*) ξ ≡ (mwks* ∘ mrens* η) ξ                   comp-mwks*-mrens*-keep
         (mrens* (keep η) ∘ mlifts*) ξ ≡ (mlifts* ∘ mrens* η) ξ                 comp-mlifts*-mrens*

                      get (subs ξ ψ) i ≡ (sub ξ ∘ get ψ) i                      comp-sub-get
                      sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟                      comp-sub-ren
                  (sub (ξ , 𝒟) ∘ wk) ℰ ≡ sub ξ ℰ                                id-cons-wk-sub
                (subs (ξ , 𝒟) ∘ wks) ψ ≡ subs ξ ψ                               id-cons-wks-subs

                      sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟                      comp-ren-sub
                     subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ                    comp-rens-subs
            (subs (lifts ξ) ∘ lifts) ψ ≡ (lifts ∘ subs ξ) ψ                     comp-lifts-subs

          (sub (mrens η ξ) ∘ mren η) 𝒟 ≡ (mren η ∘ sub ξ) 𝒟                     comp-mren-sub
        (subs (mrens η ξ) ∘ mrens η) ψ ≡ (mrens η ∘ subs ξ) ψ                   comp-mrens-subs

                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                      sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟                      comp-sub
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs
                                                                                𝐒𝟒
                                                                                𝐬𝐮𝐛

                     get (msubs ξ ψ) i ≡ (msub ξ ∘ get ψ) i                     comp-msub-get
                    get (msubs* ξ ψ) i ≡ (msub ξ ∘ get ψ) i                     comp-msub-get*
                    (ren η ∘ msub ξ) 𝒟 ≡ (msub ξ ∘ ren η) 𝒟                     comp-msub-ren
                  (rens η ∘ msubs ξ) ψ ≡ (msubs ξ ∘ rens η) ψ                   comp-msubs-rens
                   (lifts ∘ msubs ξ) ψ ≡ (msubs ξ ∘ lifts) ψ                    comp-msubs-lifts
                     msub (gets ξ η) 𝒟 ≡ (msub ξ ∘ mren η) 𝒟                    comp-msub-mren
                (msub (ξ , 𝒟) ∘ mwk) ℰ ≡ msub ξ ℰ                               id-cons-mwk-msub
              (msubs (ξ , 𝒟) ∘ mwks) ψ ≡ msubs ξ ψ                              id-cons-mwks-msubs
            (msubs* (ξ , 𝒟) ∘ mwks*) ψ ≡ msubs* ξ ψ                             id-cons-mwks*-msubs*

                    msub (mrens η ξ) 𝒟 ≡ (mren η ∘ msub ξ) 𝒟                    comp-mren-msub
                   msubs (mrens η ξ) ψ ≡ (mrens η ∘ msubs ξ) ψ                  comp-mrens-msubs
           (msubs (mlifts ξ) ∘ mwks) ψ ≡ (mwks ∘ msubs ξ) ψ                     comp-mwks-msubs
                 msubs* (mrens* η ξ) ψ ≡ (mrens* η ∘ msubs* ξ) ψ                comp-mrens*-msubs*
        (msubs* (mlifts* ξ) ∘ mwks*) ψ ≡ (mwks* ∘ msubs* ξ) ψ                   comp-mwks*-msubs*
      (msubs* (mlifts* ξ) ∘ mlifts*) ψ ≡ (mlifts* ∘ msubs* ξ) ψ                 comp-mlifts*-msubs*

          (sub (msubs ξ ψ) ∘ msub ξ) 𝒟 ≡ (msub ξ ∘ sub ψ) 𝒟                     comp-msub-sub

                          msub mids* 𝒟 ≡ 𝒟                                      id-msub
                         msubs mids* ξ ≡ ξ                                      id-msubs
                        msubs* mids* ξ ≡ ξ                                      lid-msubs
                        msubs* ξ mids* ≡ ξ                                      rid-msubs
                   msub (msubs* ξ ψ) 𝒟 ≡ (msub ξ ∘ msub ψ) 𝒟                    comp-msub
                  msubs (msubs* ξ ψ) φ ≡ (msubs ξ ∘ msubs ψ) φ                  comp-msubs
                 msubs* (msubs* ξ ψ) φ ≡ msubs* ξ (msubs* ψ φ)                  assoc-msubs
                                                                                𝐒𝟒*
                                                                                𝐦𝐬𝐮𝐛
                                                                                𝐦𝐬𝐮𝐛𝐬
-}
--------------------------------------------------------------------------------


comp-ren-get : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (i : Ξ ∋ A)
                              → get (rens η ξ) i ≡ (ren η ∘ get ξ) i
comp-ren-get η (ξ , 𝒟) zero    = refl
comp-ren-get η (ξ , ℰ) (suc i) = comp-ren-get η ξ i


comp-rens-gets : ∀ {Δ Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ′ allvalid[ Γ ]) (η₂ : Ξ′ ⊇ Ξ)
                                 → gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂
comp-rens-gets η₁ ∙       done      = refl
comp-rens-gets η₁ (ξ , ℰ) (drop η₂) = comp-rens-gets η₁ ξ η₂
comp-rens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & comp-rens-gets η₁ ξ η₂


comp-lifts-gets : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⊢ Ξ′ allvalid[ Γ ]) (η : Ξ′ ⊇ Ξ)
                                 → (gets (lifts {A} ξ) ∘ keep) η ≡ (lifts ∘ gets ξ) η
comp-lifts-gets ξ η = (_, vz) & comp-rens-gets (drop id) ξ η


get-var : ∀ {Δ Γ A} → (i : Γ ∋ A)
                    → get (ids {Δ = Δ}) i ≡ var i
get-var zero    = refl
get-var (suc i) = comp-ren-get (drop id) ids i
                ⋮ wk & get-var i
                ⋮ (\ i′ → var (suc i′)) & id-ren∋ i


--------------------------------------------------------------------------------


id-ren : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
                   → ren id 𝒟 ≡ 𝒟
id-ren (var i)      = var & id-ren∋ i
id-ren (lam 𝒟)      = lam & id-ren 𝒟
id-ren (app 𝒟 ℰ)    = app & id-ren 𝒟 ⊗ id-ren ℰ
id-ren (mvar i)     = refl
id-ren (box 𝒟)      = refl
id-ren (letbox 𝒟 ℰ) = letbox & id-ren 𝒟 ⊗ id-ren ℰ


id-rens : ∀ {Δ Γ Ξ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                    → rens id ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟


comp-ren : ∀ {Δ Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Δ ⊢ A valid[ Γ ])
                           → ren (η₁ ∘ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟
comp-ren η₁ η₂ (var i)      = var & comp-ren∋ η₁ η₂ i
comp-ren η₁ η₂ (lam 𝒟)      = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ)    = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ
comp-ren η₁ η₂ (mvar i)     = refl
comp-ren η₁ η₂ (box 𝒟)      = refl
comp-ren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ


comp-rens : ∀ {Δ Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                            → rens (η₁ ∘ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟


𝐫𝐞𝐧 : ∀ {A} → Presheaf 𝐎𝐏𝐄 (\ Γ → Σ (List Assert) (\ Δ → Δ ⊢ A valid[ Γ ]))
𝐫𝐞𝐧 = record
        { ℱ     = \ { η (Δ , 𝒟) → Δ , ren η 𝒟 }
        ; idℱ   = funext! (\ { (Δ , 𝒟) → (Δ ,_) & id-ren 𝒟 })
        ; compℱ = \ η₁ η₂ → funext! (\ { (Δ , 𝒟) → (Δ ,_) & comp-ren η₁ η₂ 𝒟 })
        }


𝐫𝐞𝐧𝐬 : ∀ {Ξ} → Presheaf 𝐎𝐏𝐄 (\ Γ → Σ (List Assert) (\ Δ → Δ ⊢ Ξ allvalid[ Γ ]))
𝐫𝐞𝐧𝐬 = record
         { ℱ     = \ { η (Δ , ξ) → Δ , rens η ξ }
         ; idℱ   = funext! (\ { (Δ , ξ) → (Δ ,_) & id-rens ξ })
         ; compℱ = \ η₁ η₂ → funext! (\ { (Δ , ξ) → (Δ ,_) & comp-rens η₁ η₂ ξ })
         }


--------------------------------------------------------------------------------


comp-wk-ren-keep : ∀ {Δ Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Δ ⊢ A valid[ Γ ])
                                  → (ren (keep {A = B} η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟
comp-wk-ren-keep η 𝒟 = comp-ren (drop id) (keep η) 𝒟 ⁻¹
                     ⋮ (\ η′ → ren (drop η′) 𝒟) & (lid∘ η ⋮ rid∘ η ⁻¹)
                     ⋮ comp-ren η (drop id) 𝒟


comp-wks-rens-keep : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                                    → (rens (keep {A = A} η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ
comp-wks-rens-keep η ∙       = refl
comp-wks-rens-keep η (ξ , 𝒟) = _,_ & comp-wks-rens-keep η ξ ⊗ comp-wk-ren-keep η 𝒟


comp-lifts-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                                 → (rens (keep {A = A} η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ
comp-lifts-rens η ξ = (_, vz) & comp-wks-rens-keep η ξ


--------------------------------------------------------------------------------


comp-ren-mren : ∀ {Δ Δ′ Γ Γ′ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (𝒟 : Δ ⊢ A valid[ Γ ])
                                → (mren η₁ ∘ ren η₂) 𝒟 ≡ (ren η₂ ∘ mren η₁) 𝒟
comp-ren-mren η₁ η₂ (var i)      = refl
comp-ren-mren η₁ η₂ (lam 𝒟)      = lam & comp-ren-mren η₁ (keep η₂) 𝒟
comp-ren-mren η₁ η₂ (app 𝒟 ℰ)    = app & comp-ren-mren η₁ η₂ 𝒟 ⊗ comp-ren-mren η₁ η₂ ℰ
comp-ren-mren η₁ η₂ (mvar i)     = refl
comp-ren-mren η₁ η₂ (box 𝒟)      = refl
comp-ren-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-ren-mren η₁ η₂ 𝒟 ⊗ comp-ren-mren (keep η₁) η₂ ℰ


comp-rens-mrens : ∀ {Δ Δ′ Γ Γ′ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                                  → (mrens η₁ ∘ rens η₂) ξ ≡ (rens η₂ ∘ mrens η₁) ξ
comp-rens-mrens η₁ η₂ ∙       = refl
comp-rens-mrens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens-mrens η₁ η₂ ξ ⊗ comp-ren-mren η₁ η₂ 𝒟


comp-lifts-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                                  → (mrens η ∘ lifts {A}) ξ ≡ (lifts ∘ mrens η) ξ
comp-lifts-mrens η ξ = (_, vz) & comp-rens-mrens η (drop id) ξ


id-mrens-ids : ∀ {Δ Δ′ Γ} → (η : Δ′ ⊇ Δ)
                          → mrens η (ids {Γ = Γ}) ≡ ids
id-mrens-ids {Γ = ∙}     η = refl
id-mrens-ids {Γ = Γ , A} η = comp-lifts-mrens η ids
                           ⋮ lifts & id-mrens-ids η


--------------------------------------------------------------------------------


comp-mren-get : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (i : Ξ ∋ A)
                               → get (mrens η ξ) i ≡ (mren η ∘ get ξ) i
comp-mren-get η (ξ , 𝒟) zero    = refl
comp-mren-get η (ξ , ℰ) (suc i) = comp-mren-get η ξ i


comp-mren-get* : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*) (i : Ξ ∋ ⟪⊫ A ⟫)
                              → get (mrens* η ξ) i ≡ (mren η ∘ get ξ) i
comp-mren-get* η (ξ , 𝒟) zero    = refl
comp-mren-get* η (ξ , ℰ) (suc i) = comp-mren-get* η ξ i


comp-mrens-gets : ∀ {Δ Δ′ Γ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ′ allvalid[ Γ ]) (η₂ : Ξ′ ⊇ Ξ)
                                  → gets (mrens η₁ ξ) η₂ ≡ (mrens η₁ ∘ gets ξ) η₂
comp-mrens-gets η₁ ∙       done      = refl
comp-mrens-gets η₁ (ξ , ℰ) (drop η₂) = comp-mrens-gets η₁ ξ η₂
comp-mrens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & comp-mrens-gets η₁ ξ η₂


comp-mrens*-gets : ∀ {Δ Δ′ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ′ allvalid*) (η₂ : Ξ′ ⊇ Ξ)
                                 → gets (mrens* η₁ ξ) η₂ ≡ (mrens* η₁ ∘ gets ξ) η₂
comp-mrens*-gets η₁ ∙       done      = refl
comp-mrens*-gets η₁ (ξ , ℰ) (drop η₂) = comp-mrens*-gets η₁ ξ η₂
comp-mrens*-gets η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & comp-mrens*-gets η₁ ξ η₂


comp-mlifts*-gets : ∀ {Δ Ξ Ξ′ A} → (ξ : Δ ⊢ Ξ′ allvalid*) (η : Ξ′ ⊇ Ξ)
                                 → (gets (mlifts* {A} ξ) ∘ keep) η ≡ (mlifts* ∘ gets ξ) η
comp-mlifts*-gets ξ η = (_, mvz) & comp-mrens*-gets (drop id) ξ η


get-mvar : ∀ {Δ A} → (i : Δ ∋ A)
                   → get mids* i ≡ mvar i
get-mvar zero    = refl
get-mvar (suc i) = comp-mren-get* (drop id) mids* i
                 ⋮ mwk & get-mvar i
                 ⋮ (\ i′ → mvar (suc i′)) & id-ren∋ i


--------------------------------------------------------------------------------


id-mren : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
                    → mren id 𝒟 ≡ 𝒟
id-mren (var i)      = refl
id-mren (lam 𝒟)      = lam & id-mren 𝒟
id-mren (app 𝒟 ℰ)    = app & id-mren 𝒟 ⊗ id-mren ℰ
id-mren (mvar i)     = mvar & id-ren∋ i
id-mren (box 𝒟)      = box & id-mren 𝒟
id-mren (letbox 𝒟 ℰ) = letbox & id-mren 𝒟 ⊗ id-mren ℰ


id-mrens : ∀ {Δ Γ Ξ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                     → mrens id ξ ≡ ξ
id-mrens ∙       = refl
id-mrens (ξ , 𝒟) = _,_ & id-mrens ξ ⊗ id-mren 𝒟


comp-mren : ∀ {Δ Δ′ Δ″ Γ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (𝒟 : Δ ⊢ A valid[ Γ ])
                            → mren (η₁ ∘ η₂) 𝒟 ≡ (mren η₂ ∘ mren η₁) 𝒟
comp-mren η₁ η₂ (var i)      = refl
comp-mren η₁ η₂ (lam 𝒟)      = lam & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (app 𝒟 ℰ)    = app & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren η₁ η₂ ℰ
comp-mren η₁ η₂ (mvar i)     = mvar & comp-ren∋ η₁ η₂ i
comp-mren η₁ η₂ (box 𝒟)      = box & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren (keep η₁) (keep η₂) ℰ


comp-mrens : ∀ {Δ Δ′ Δ″ Γ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                             → mrens (η₁ ∘ η₂) ξ ≡ (mrens η₂ ∘ mrens η₁) ξ
comp-mrens η₁ η₂ ∙       = refl
comp-mrens η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens η₁ η₂ ξ ⊗ comp-mren η₁ η₂ 𝒟


𝐦𝐫𝐞𝐧 : ∀ {A} → Presheaf 𝐎𝐏𝐄 (\ Δ → Σ (List Prop) (\ Γ → Δ ⊢ A valid[ Γ ]))
𝐦𝐫𝐞𝐧 = record
         { ℱ     = \ { η (Γ , 𝒟) → Γ , mren η 𝒟 }
         ; idℱ   = funext! (\ { (Γ , 𝒟) → (Γ ,_) & id-mren 𝒟 })
         ; compℱ = \ η₁ η₂ → funext! (\ { (Γ , 𝒟) → (Γ ,_) & comp-mren η₁ η₂ 𝒟 })
         }


𝐦𝐫𝐞𝐧𝐬 : ∀ {Ξ} → Presheaf 𝐎𝐏𝐄 (\ Δ → Σ (List Prop) (\ Γ → Δ ⊢ Ξ allvalid[ Γ ]))
𝐦𝐫𝐞𝐧𝐬 = record
          { ℱ     = \ { η (Γ , ξ) → Γ , mrens η ξ}
          ; idℱ   = funext! (\ { (Γ , ξ) → (Γ ,_) & id-mrens ξ })
          ; compℱ = \ η₁ η₂ → funext! (\ { (Γ , ξ) → (Γ ,_) & comp-mrens η₁ η₂ ξ })
          }


--------------------------------------------------------------------------------


comp-mwk-mren-keep : ∀ {Δ Δ′ Γ A B} → (η : Δ′ ⊇ Δ) (𝒟 : Δ ⊢ A valid[ Γ ])
                                    → (mren (keep {A = B} η) ∘ mwk) 𝒟 ≡ (mwk ∘ mren η) 𝒟
comp-mwk-mren-keep η 𝒟 = comp-mren (drop id) (keep η) 𝒟 ⁻¹
                       ⋮ (\ η′ → mren (drop η′) 𝒟) & (lid∘ η ⋮ rid∘ η ⁻¹)
                       ⋮ comp-mren η (drop id) 𝒟


comp-mwks-mrens-keep : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                                      → (mrens (keep {A = A} η) ∘ mwks) ξ ≡ (mwks ∘ mrens η) ξ
comp-mwks-mrens-keep η ∙       = refl
comp-mwks-mrens-keep η (ξ , 𝒟) = _,_ & comp-mwks-mrens-keep η ξ ⊗ comp-mwk-mren-keep η 𝒟


comp-mwks*-mrens*-keep : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*)
                                      → (mrens* (keep {A = A} η) ∘ mwks*) ξ ≡ (mwks* ∘ mrens* η) ξ
comp-mwks*-mrens*-keep η ∙       = refl
comp-mwks*-mrens*-keep η (ξ , 𝒟) = _,_ & comp-mwks*-mrens*-keep η ξ ⊗ comp-mwk-mren-keep η 𝒟


comp-mlifts*-mrens* : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*)
                                   → (mrens* (keep {A = A} η) ∘ mlifts*) ξ ≡ (mlifts* ∘ mrens* η) ξ
comp-mlifts*-mrens* η ξ = (_, mvz) & comp-mwks*-mrens*-keep η ξ


--------------------------------------------------------------------------------


comp-sub-get : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ]) (i : Ψ ∋ A)
                             → get (subs ξ ψ) i ≡ (sub ξ ∘ get ψ) i
comp-sub-get ξ (ψ , 𝒟) zero    = refl
comp-sub-get ξ (ψ , ℰ) (suc i) = comp-sub-get ξ ψ i


comp-sub-ren : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⊢ Ξ′ allvalid[ Γ ]) (η : Ξ′ ⊇ Ξ) (𝒟 : Δ ⊢ A valid[ Ξ ])
                              → sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟
comp-sub-ren ξ η (var i)      = comp-get-ren∋ ξ η i
comp-sub-ren ξ η (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-gets ξ η ⁻¹
                                      ⋮ comp-sub-ren (lifts ξ) (keep η) 𝒟
                                      )
comp-sub-ren ξ η (app 𝒟 ℰ)    = app & comp-sub-ren ξ η 𝒟 ⊗ comp-sub-ren ξ η ℰ
comp-sub-ren ξ η (mvar i)     = refl
comp-sub-ren ξ η (box 𝒟)      = refl
comp-sub-ren ξ η (letbox 𝒟 ℰ) = letbox & comp-sub-ren ξ η 𝒟
                                       ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mrens-gets (drop id) ξ η ⁻¹
                                         ⋮ comp-sub-ren (mwks ξ) η ℰ
                                         )


id-cons-wk-sub : ∀ {Δ Γ Ξ A B} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (𝒟 : Δ ⊢ A valid[ Γ ]) (ℰ : Δ ⊢ B valid[ Ξ ])
                               → sub (ξ , 𝒟) (wk ℰ) ≡ sub ξ ℰ
id-cons-wk-sub ξ 𝒟 ℰ = comp-sub-ren (ξ , 𝒟) (drop id) ℰ ⁻¹
                     ⋮ (\ ξ′ → sub ξ′ ℰ) & id-gets ξ


id-cons-wks-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (𝒟 : Δ ⊢ A valid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ])
                                 → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
id-cons-wks-subs ξ 𝒟 ∙       = refl
id-cons-wks-subs ξ 𝒟 (ψ , ℰ) = _,_ & id-cons-wks-subs ξ 𝒟 ψ ⊗ id-cons-wk-sub ξ 𝒟 ℰ


--------------------------------------------------------------------------------


comp-ren-sub : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (𝒟 : Δ ⊢ A valid[ Ξ ])
                              → sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟
comp-ren-sub η ξ (var i)      = comp-ren-get η ξ i
comp-ren-sub η ξ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-rens η ξ ⁻¹
                                      ⋮ comp-ren-sub (keep η) (lifts ξ) 𝒟
                                      )
comp-ren-sub η ξ (app 𝒟 ℰ)    = app & comp-ren-sub η ξ 𝒟 ⊗ comp-ren-sub η ξ ℰ
comp-ren-sub η ξ (mvar i)     = refl
comp-ren-sub η ξ (box 𝒟)      = refl
comp-ren-sub η ξ (letbox 𝒟 ℰ) = letbox & comp-ren-sub η ξ 𝒟
                                       ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-rens-mrens (drop id) η ξ
                                         ⋮ comp-ren-sub η (mwks ξ) ℰ
                                         )


comp-rens-subs : ∀ {Δ Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ])
                                → subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ
comp-rens-subs η ξ ∙       = refl
comp-rens-subs η ξ (ψ , 𝒟) = _,_ & comp-rens-subs η ξ ψ ⊗ comp-ren-sub η ξ 𝒟


comp-lifts-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ])
                                → (subs (lifts {A} ξ) ∘ lifts) ψ ≡ (lifts ∘ subs ξ) ψ
comp-lifts-subs ξ ψ = (_, vz) & ( id-cons-wks-subs (wks ξ) vz ψ
                                ⋮ comp-rens-subs (drop id) ξ ψ
                                )


--------------------------------------------------------------------------------


comp-mren-sub : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (𝒟 : Δ ⊢ A valid[ Ξ ])
                               → (sub (mrens η ξ) ∘ mren η) 𝒟 ≡ (mren η ∘ sub ξ) 𝒟
comp-mren-sub η ξ (var i)      = comp-mren-get η ξ i
comp-mren-sub η ξ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ (mren η 𝒟)) & comp-lifts-mrens η ξ ⁻¹
                                       ⋮ comp-mren-sub η (lifts ξ) 𝒟
                                       )
comp-mren-sub η ξ (app 𝒟 ℰ)    = app & comp-mren-sub η ξ 𝒟 ⊗ comp-mren-sub η ξ ℰ
comp-mren-sub η ξ (mvar i)     = refl
comp-mren-sub η ξ (box 𝒟)      = refl
comp-mren-sub η ξ (letbox 𝒟 ℰ) = letbox & comp-mren-sub η ξ 𝒟
                                        ⊗ ( (\ ξ′ → sub ξ′ (mren (keep η) ℰ)) & comp-mwks-mrens-keep η ξ ⁻¹
                                          ⋮ comp-mren-sub (keep η) (mwks ξ) ℰ
                                          )


comp-mrens-subs : ∀ {Δ Δ′ Γ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ])
                                 → (subs (mrens η ξ) ∘ mrens η) ψ ≡ (mrens η ∘ subs ξ) ψ
comp-mrens-subs η ξ ∙       = refl
comp-mrens-subs η ξ (ψ , 𝒟) = _,_ & comp-mrens-subs η ξ ψ ⊗ comp-mren-sub η ξ 𝒟


--------------------------------------------------------------------------------


id-sub : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
                   → sub ids 𝒟 ≡ 𝒟
id-sub (var i)      = get-var i
id-sub (lam 𝒟)      = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ)    = app & id-sub 𝒟 ⊗ id-sub ℰ
id-sub (mvar i)     = refl
id-sub (box 𝒟)      = refl
id-sub (letbox 𝒟 ℰ) = letbox & id-sub 𝒟 ⊗ ( (\ ξ′ → sub ξ′ ℰ) & id-mrens-ids (drop id)
                                          ⋮ id-sub ℰ
                                          )


comp-sub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ]) (𝒟 : Δ ⊢ A valid[ Ψ ])
                         → sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟
comp-sub ξ ψ (var i)      = comp-sub-get ξ ψ i
comp-sub ξ ψ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-subs ξ ψ ⁻¹
                                  ⋮ comp-sub (lifts ξ) (lifts ψ) 𝒟
                                  )
comp-sub ξ ψ (app 𝒟 ℰ)    = app & comp-sub ξ ψ 𝒟 ⊗ comp-sub ξ ψ ℰ
comp-sub ξ ψ (mvar i)     = refl
comp-sub ξ ψ (box 𝒟)      = refl
comp-sub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-sub ξ ψ 𝒟
                                   ⊗ ( (\ ξ′ → sub ξ′ ℰ) & comp-mrens-subs (drop id) ξ ψ ⁻¹
                                     ⋮ comp-sub (mwks ξ) (mwks ψ) ℰ
                                     )


lid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                     → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟


rid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                     → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( id-cons-wks-subs ξ 𝒟 ids
                            ⋮ rid-subs ξ
                            )


assoc-subs : ∀ {Δ Γ Ξ Ψ Φ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ]) (ψ : Δ ⊢ Ψ allvalid[ Ξ ]) (φ : Δ ⊢ Φ allvalid[ Ψ ])
                           → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ comp-sub ξ ψ 𝒟


instance
  𝐒𝟒 : ∀ {Δ} → Category (List Prop) (\ Γ Ξ → Δ ⊢ Ξ allvalid[ Γ ])
  𝐒𝟒 = record
         { id     = ids
         ; _∘_    = flip subs
         ; lid∘   = rid-subs
         ; rid∘   = lid-subs
         ; assoc∘ = \ φ ψ ξ → assoc-subs ξ ψ φ ⁻¹
         }


𝐬𝐮𝐛 : ∀ {Δ A} → Presheaf (𝐒𝟒 {Δ}) (\ Γ → Δ ⊢ A valid[ Γ ])
𝐬𝐮𝐛 = record
        { ℱ     = sub
        ; idℱ   = funext! id-sub
        ; compℱ = \ ψ ξ → funext! (comp-sub ξ ψ)
        }


--------------------------------------------------------------------------------


comp-msub-get : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid[ Γ ]) (i : Ψ ∋ A)
                              → get (msubs ξ ψ) i ≡ (msub ξ ∘ get ψ) i
comp-msub-get ξ (ψ , 𝒟) zero    = refl
comp-msub-get ξ (ψ , ℰ) (suc i) = comp-msub-get ξ ψ i


comp-msub-get* : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*) (i : Ψ ∋ ⟪⊫ A ⟫)
                             → get (msubs* ξ ψ) i ≡ (msub ξ ∘ get ψ) i
comp-msub-get* ξ (ψ , 𝒟) zero    = refl
comp-msub-get* ξ (ψ , ℰ) (suc i) = comp-msub-get* ξ ψ i


comp-msub-ren : ∀ {Δ Γ Γ′ Ξ A} → (ξ : Δ ⊢ Ξ allvalid*) (η : Γ′ ⊇ Γ) (𝒟 : Ξ ⊢ A valid[ Γ ])
                               → (ren η ∘ msub ξ) 𝒟 ≡ (msub ξ ∘ ren η) 𝒟
comp-msub-ren ξ η (var i)      = refl
comp-msub-ren ξ η (lam 𝒟)      = lam & comp-msub-ren ξ (keep η) 𝒟
comp-msub-ren ξ η (app 𝒟 ℰ)    = app & comp-msub-ren ξ η 𝒟 ⊗ comp-msub-ren ξ η ℰ
comp-msub-ren ξ η (mvar i)     = comp-ren-sub η ∙ (get ξ i) ⁻¹
comp-msub-ren ξ η (box 𝒟)      = refl
comp-msub-ren ξ η (letbox 𝒟 ℰ) = letbox & comp-msub-ren ξ η 𝒟 ⊗ comp-msub-ren (mlifts* ξ) η ℰ


comp-msubs-rens : ∀ {Δ Γ Γ′ Ξ Ψ} → (ξ : Δ ⊢ Ξ allvalid*) (η : Γ′ ⊇ Γ) (ψ : Ξ ⊢ Ψ allvalid[ Γ ])
                                 → (rens η ∘ msubs ξ) ψ ≡ (msubs ξ ∘ rens η) ψ
comp-msubs-rens ξ η ∙       = refl
comp-msubs-rens ξ η (ψ , 𝒟) = _,_ & comp-msubs-rens ξ η ψ ⊗ comp-msub-ren ξ η 𝒟


comp-msubs-lifts : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid[ Γ ])
                                 → (lifts {A} ∘ msubs ξ) ψ ≡ (msubs ξ ∘ lifts) ψ
comp-msubs-lifts ξ ψ = (_, vz) & comp-msubs-rens ξ (drop id) ψ


comp-msub-mren : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⊢ Ξ′ allvalid*) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A valid[ Γ ])
                                → msub (gets ξ η) 𝒟 ≡ (msub ξ ∘ mren η) 𝒟
comp-msub-mren ξ η (var i)      = refl
comp-msub-mren ξ η (lam 𝒟)      = lam & comp-msub-mren ξ η 𝒟
comp-msub-mren ξ η (app 𝒟 ℰ)    = app & comp-msub-mren ξ η 𝒟 ⊗ comp-msub-mren ξ η ℰ
comp-msub-mren ξ η (mvar i)     = sub ∙ & comp-get-ren∋ ξ η i
comp-msub-mren ξ η (box 𝒟)      = box & comp-msub-mren ξ η 𝒟
comp-msub-mren ξ η (letbox 𝒟 ℰ) = letbox & comp-msub-mren ξ η 𝒟
                                         ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts*-gets ξ η ⁻¹
                                           ⋮ comp-msub-mren (mlifts* ξ) (keep η) ℰ
                                           )


id-cons-mwk-msub : ∀ {Δ Γ Ξ A B} → (ξ : Δ ⊢ Ξ allvalid*) (𝒟 : Δ ⊢ A valid[ ∙ ]) (ℰ : Ξ ⊢ B valid[ Γ ])
                                 → (msub (ξ , 𝒟) ∘ mwk) ℰ ≡ msub ξ ℰ
id-cons-mwk-msub ξ 𝒟 ℰ = comp-msub-mren (ξ , 𝒟) (drop id) ℰ ⁻¹
                       ⋮ (\ ξ′ → msub ξ′ ℰ) & id-gets ξ


id-cons-mwks-msubs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (𝒟 : Δ ⊢ A valid[ ∙ ]) (ψ : Ξ ⊢ Ψ allvalid[ Γ ])
                                   → (msubs (ξ , 𝒟) ∘ mwks) ψ ≡ msubs ξ ψ
id-cons-mwks-msubs ξ 𝒟 ∙       = refl
id-cons-mwks-msubs ξ 𝒟 (ψ , ℰ) = _,_ & id-cons-mwks-msubs ξ 𝒟 ψ ⊗ id-cons-mwk-msub ξ 𝒟 ℰ


id-cons-mwks*-msubs* : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (𝒟 : Δ ⊢ A valid[ ∙ ]) (ψ : Ξ ⊢ Ψ allvalid*)
                                   → (msubs* (ξ , 𝒟) ∘ mwks*) ψ ≡ msubs* ξ ψ
id-cons-mwks*-msubs* ξ 𝒟 ∙       = refl
id-cons-mwks*-msubs* ξ 𝒟 (ψ , ℰ) = _,_ & id-cons-mwks*-msubs* ξ 𝒟 ψ ⊗ id-cons-mwk-msub ξ 𝒟 ℰ


--------------------------------------------------------------------------------


comp-mren-msub : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*) (𝒟 : Ξ ⊢ A valid[ Γ ])
                                → msub (mrens* η ξ) 𝒟 ≡ (mren η ∘ msub ξ) 𝒟
comp-mren-msub η ξ (var i)      = refl
comp-mren-msub η ξ (lam 𝒟)      = lam & comp-mren-msub η ξ 𝒟
comp-mren-msub η ξ (app 𝒟 ℰ)    = app & comp-mren-msub η ξ 𝒟 ⊗ comp-mren-msub η ξ ℰ
comp-mren-msub η ξ (mvar i)     = sub ∙ & comp-mren-get* η ξ i
                                ⋮ comp-mren-sub η ∙ (get ξ i)
comp-mren-msub η ξ (box 𝒟)      = box & comp-mren-msub η ξ 𝒟
comp-mren-msub η ξ (letbox 𝒟 ℰ) = letbox & comp-mren-msub η ξ 𝒟
                                         ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts*-mrens* η ξ ⁻¹
                                           ⋮ comp-mren-msub (keep η) (mlifts* ξ) ℰ
                                           )


comp-mrens-msubs : ∀ {Δ Δ′ Γ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid[ Γ ])
                                  → msubs (mrens* η ξ) ψ ≡ (mrens η ∘ msubs ξ) ψ
comp-mrens-msubs η ξ ∙       = refl
comp-mrens-msubs η ξ (ψ , 𝒟) = _,_ & comp-mrens-msubs η ξ ψ ⊗ comp-mren-msub η ξ 𝒟


comp-mwks-msubs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid[ Γ ])
                                → (msubs (mlifts* {A} ξ) ∘ mwks) ψ ≡ (mwks ∘ msubs ξ) ψ
comp-mwks-msubs ξ ψ = id-cons-mwks-msubs (mwks* ξ) mvz ψ
                    ⋮ comp-mrens-msubs (drop id) ξ ψ


comp-mrens*-msubs* : ∀ {Δ Δ′ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*)
                                  → msubs* (mrens* η ξ) ψ ≡ (mrens* η ∘ msubs* ξ) ψ
comp-mrens*-msubs* η ξ ∙       = refl
comp-mrens*-msubs* η ξ (ψ , 𝒟) = _,_ & comp-mrens*-msubs* η ξ ψ ⊗ comp-mren-msub η ξ 𝒟


comp-mwks*-msubs* : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*)
                                → (msubs* (mlifts* {A} ξ) ∘ mwks*) ψ ≡ (mwks* ∘ msubs* ξ) ψ
comp-mwks*-msubs* ξ ψ = id-cons-mwks*-msubs* (mwks* ξ) mvz ψ
                      ⋮ comp-mrens*-msubs* (drop id) ξ ψ


comp-mlifts*-msubs* : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*)
                                  → (msubs* (mlifts* {A} ξ) ∘ mlifts*) ψ ≡ (mlifts* ∘ msubs* ξ) ψ
comp-mlifts*-msubs* ξ ψ = (_, mvz) & comp-mwks*-msubs* ξ ψ


--------------------------------------------------------------------------------


comp-msub-sub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid[ Γ ]) (𝒟 : Ξ ⊢ A valid[ Ψ ])
                              → (sub (msubs ξ ψ) ∘ msub ξ) 𝒟 ≡ (msub ξ ∘ sub ψ) 𝒟
comp-msub-sub ξ ψ (var i)      = comp-msub-get ξ ψ i
comp-msub-sub ξ ψ (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ (msub ξ 𝒟)) & comp-msubs-lifts ξ ψ
                                       ⋮ comp-msub-sub ξ (lifts ψ) 𝒟
                                       )
comp-msub-sub ξ ψ (app 𝒟 ℰ)    = app & comp-msub-sub ξ ψ 𝒟 ⊗ comp-msub-sub ξ ψ ℰ
comp-msub-sub ξ ψ (mvar i)     = comp-sub (msubs ξ ψ) ∙ (get ξ i) ⁻¹
comp-msub-sub ξ ψ (box 𝒟)      = refl
comp-msub-sub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-msub-sub ξ ψ 𝒟
                                        ⊗ ( (\ ξ′ → sub ξ′ (msub (mwks* ξ , mvz) ℰ)) & comp-mwks-msubs ξ ψ ⁻¹
                                          ⋮ comp-msub-sub (mlifts* ξ) (mwks ψ) ℰ
                                          )


--------------------------------------------------------------------------------


id-msub : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
                    → msub mids* 𝒟 ≡ 𝒟
id-msub (var i)      = refl
id-msub (lam 𝒟)      = lam & id-msub 𝒟
id-msub (app 𝒟 ℰ)    = app & id-msub 𝒟 ⊗ id-msub ℰ
id-msub (mvar i)     = sub ∙ & get-mvar i
id-msub (box 𝒟)      = box & id-msub 𝒟
id-msub (letbox 𝒟 ℰ) = letbox & id-msub 𝒟 ⊗ id-msub ℰ


id-msubs : ∀ {Δ Γ Ξ} → (ξ : Δ ⊢ Ξ allvalid[ Γ ])
                     → msubs mids* ξ ≡ ξ
id-msubs ∙       = refl
id-msubs (ξ , 𝒟) = _,_ & id-msubs ξ ⊗ id-msub 𝒟


lid-msubs* : ∀ {Δ Ξ} → (ξ : Δ ⊢ Ξ allvalid*)
                     → msubs* mids* ξ ≡ ξ
lid-msubs* ∙       = refl
lid-msubs* (ξ , 𝒟) = _,_ & lid-msubs* ξ ⊗ id-msub 𝒟


rid-msubs* : ∀ {Δ Ξ} → (ξ : Δ ⊢ Ξ allvalid*)
                     → msubs* ξ mids* ≡ ξ
rid-msubs* ∙       = refl
rid-msubs* (ξ , 𝒟) = _,_ & ( id-cons-mwks*-msubs* ξ 𝒟 mids*
                           ⋮ rid-msubs* ξ
                           )
                         ⊗ id-sub 𝒟


comp-msub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*) (𝒟 : Ψ ⊢ A valid[ Γ ])
                          → msub (msubs* ξ ψ) 𝒟 ≡ (msub ξ ∘ msub ψ) 𝒟
comp-msub ξ ψ (var i)      = refl
comp-msub ξ ψ (lam 𝒟)      = lam & comp-msub ξ ψ 𝒟
comp-msub ξ ψ (app 𝒟 ℰ)    = app & comp-msub ξ ψ 𝒟 ⊗ comp-msub ξ ψ ℰ
comp-msub ξ ψ (mvar i)     = sub ∙ & comp-msub-get* ξ ψ i
                           ⋮ comp-msub-sub ξ ∙ (get ψ i)
comp-msub ξ ψ (box 𝒟)      = box & comp-msub ξ ψ 𝒟
comp-msub ξ ψ (letbox 𝒟 ℰ) = letbox & comp-msub ξ ψ 𝒟
                                    ⊗ ( (\ ξ′ → msub ξ′ ℰ) & comp-mlifts*-msubs* ξ ψ ⁻¹
                                      ⋮ comp-msub (mlifts* ξ) (mlifts* ψ) ℰ
                                      )


comp-msubs : ∀ {Δ Γ Ξ Ψ Φ} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*) (φ : Ψ ⊢ Φ allvalid[ Γ ])
                           → msubs (msubs* ξ ψ) φ ≡ (msubs ξ ∘ msubs ψ) φ
comp-msubs ξ ψ ∙       = refl
comp-msubs ξ ψ (φ , 𝒟) = _,_ & comp-msubs ξ ψ φ ⊗ comp-msub ξ ψ 𝒟


assoc-msubs* : ∀ {Δ Ξ Ψ Φ} → (ξ : Δ ⊢ Ξ allvalid*) (ψ : Ξ ⊢ Ψ allvalid*) (φ : Ψ ⊢ Φ allvalid*)
                           → msubs* (msubs* ξ ψ) φ ≡ msubs* ξ (msubs* ψ φ)
assoc-msubs* ξ ψ ∙       = refl
assoc-msubs* ξ ψ (φ , 𝒟) = _,_ & assoc-msubs* ξ ψ φ ⊗ comp-msub ξ ψ 𝒟


instance
  𝐒𝟒* : Category (List Assert) _⊢_allvalid*
  𝐒𝟒* = record
          { id     = mids*
          ; _∘_    = flip msubs*
          ; lid∘   = rid-msubs*
          ; rid∘   = lid-msubs*
          ; assoc∘ = \ φ ψ ξ → assoc-msubs* ξ ψ φ ⁻¹
          }


𝐦𝐬𝐮𝐛 : ∀ {A} → Presheaf 𝐒𝟒* (_⊢ A valid[ ∙ ])
𝐦𝐬𝐮𝐛 = record
         { ℱ     = msub
         ; idℱ   = funext! id-msub
         ; compℱ = \ ψ ξ → funext! (comp-msub ξ ψ)
         }


𝐦𝐬𝐮𝐛𝐬 : ∀ {Γ Ξ} → Presheaf 𝐒𝟒* (_⊢ Ξ allvalid[ Γ ])
𝐦𝐬𝐮𝐛𝐬 = record
          { ℱ     = msubs
          ; idℱ   = funext! id-msubs
          ; compℱ = \ ψ ξ → funext! (comp-msubs ξ ψ)
          }


--------------------------------------------------------------------------------
