module IPLLemmas where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import AllListLemmas
open import IPLPropositions
open import IPLDerivations


--------------------------------------------------------------------------------
{-
                      get (rens η ξ) i ≡ (ren η ∘ get ξ) i                      comp-ren-get
                   gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂                  comp-rens-gets
               gets (lifts ξ) (keep η) ≡ (lifts ∘ gets ξ) η                     comp-lifts-gets
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

                      get (subs ξ ψ) i ≡ (sub ξ ∘ get ψ) i                      comp-sub-get
                      sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟                      comp-sub-ren

                    sub (ξ , 𝒟) (wk ℰ) ≡ sub ξ ℰ                                id-cons-wk-sub
                  subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ                               id-cons-wks-subs

                      sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟                      comp-ren-sub
                     subs (rens η ξ) ψ = (rens η ∘ subs ξ) ψ                    comp-rens-subs
              subs (lifts ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ                     comp-lifts-subs

                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                      sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟                      comp-sub
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs
                                                                                𝐈𝐏𝐋
                                                                                𝐬𝐮𝐛
-}
--------------------------------------------------------------------------------


comp-ren-get : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ alltrue) (i : Ξ ∋ A)
                            → get (rens η ξ) i ≡ (ren η ∘ get ξ) i
comp-ren-get η (ξ , 𝒟) zero    = refl
comp-ren-get η (ξ , 𝒟) (suc i) = comp-ren-get η ξ i


comp-rens-gets : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ′ alltrue) (η₂ : Ξ′ ⊇ Ξ)
                               → gets (rens η₁ ξ) η₂ ≡ (rens η₁ ∘ gets ξ) η₂
comp-rens-gets η₁ ∙       done      = refl
comp-rens-gets η₁ (ξ , 𝒟) (drop η₂) = comp-rens-gets η₁ ξ η₂
comp-rens-gets η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & comp-rens-gets η₁ ξ η₂


comp-lifts-gets : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢ Ξ′ alltrue) (η : Ξ′ ⊇ Ξ)
                               → gets (lifts {A} ξ) (keep η) ≡ (lifts ∘ gets ξ) η
comp-lifts-gets ξ η = (_, vz) & comp-rens-gets (drop id) ξ η


get-var : ∀ {Γ A} → (i : Γ ∋ A)
                  → get ids i ≡ var i
get-var zero    = refl
get-var (suc i) = comp-ren-get (drop id) ids i
                ⋮ wk & get-var i
                ⋮ (\ i′ → var (suc i′)) & id-ren∋ i


--------------------------------------------------------------------------------


id-ren : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → ren id 𝒟 ≡ 𝒟
id-ren (var i)   = var & id-ren∋ i
id-ren (lam 𝒟)   = lam & id-ren 𝒟
id-ren (app 𝒟 ℰ) = app & id-ren 𝒟 ⊗ id-ren ℰ


id-rens : ∀ {Γ Ξ} → (ξ : Γ ⊢ Ξ alltrue)
                  → rens id ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟


comp-ren : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Γ ⊢ A true)
                         → ren (η₁ ∘ η₂) 𝒟 ≡ (ren η₂ ∘ ren η₁) 𝒟
comp-ren η₁ η₂ (var i)   = var & comp-ren∋ η₁ η₂ i
comp-ren η₁ η₂ (lam 𝒟)   = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ) = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ


comp-rens : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Γ ⊢ Ξ alltrue)
                          → rens (η₁ ∘ η₂) ξ ≡ (rens η₂ ∘ rens η₁) ξ
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟


𝐫𝐞𝐧 : ∀ {A} → Presheaf 𝐎𝐏𝐄 (_⊢ A true)
𝐫𝐞𝐧 = record
        { ℱ     = ren
        ; idℱ   = funext! id-ren
        ; compℱ = \ η₁ η₂ → funext! (comp-ren η₁ η₂)
        }


𝐫𝐞𝐧𝐬 : ∀ {Ξ} → Presheaf 𝐎𝐏𝐄 (_⊢ Ξ alltrue)
𝐫𝐞𝐧𝐬 = record
         { ℱ     = rens
         ; idℱ   = funext! id-rens
         ; compℱ = \ η₁ η₂ → funext! (comp-rens η₁ η₂)
         }


--------------------------------------------------------------------------------


comp-wk-ren-keep : ∀ {Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (𝒟 : Γ ⊢ A true)
                                → (ren (keep {A = B} η) ∘ wk) 𝒟 ≡ (wk ∘ ren η) 𝒟
comp-wk-ren-keep η 𝒟 = comp-ren (drop id) (keep η) 𝒟 ⁻¹
                     ⋮ (\ η′ → ren (drop η′) 𝒟) & (lid∘ η ⋮ rid∘ η ⁻¹)
                     ⋮ comp-ren η (drop id) 𝒟


comp-wks-rens-keep : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ alltrue)
                                  → (rens (keep {A = A} η) ∘ wks) ξ ≡ (wks ∘ rens η) ξ
comp-wks-rens-keep η ∙       = refl
comp-wks-rens-keep η (ξ , 𝒟) = _,_ & comp-wks-rens-keep η ξ ⊗ comp-wk-ren-keep η 𝒟


comp-lifts-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ alltrue)
                               → (rens (keep {A = A} η) ∘ lifts) ξ ≡ (lifts ∘ rens η) ξ
comp-lifts-rens η ξ = (_, vz) & comp-wks-rens-keep η ξ


--------------------------------------------------------------------------------


comp-sub-get : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢ Ξ alltrue) (ψ : Ξ ⊢ Ψ alltrue) (i : Ψ ∋ A)
                           → get (subs ξ ψ) i ≡ (sub ξ ∘ get ψ) i
comp-sub-get ξ (ψ , 𝒟) zero    = refl
comp-sub-get ξ (ψ , ℰ) (suc i) = comp-sub-get ξ ψ i


comp-sub-ren : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢ Ξ′ alltrue) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                            → sub (gets ξ η) 𝒟 ≡ (sub ξ ∘ ren η) 𝒟
comp-sub-ren ξ η (var i)   = comp-get-ren∋ ξ η i
comp-sub-ren ξ η (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-gets ξ η ⁻¹
                                   ⋮ comp-sub-ren (lifts ξ) (keep η) 𝒟
                                   )
comp-sub-ren ξ η (app 𝒟 ℰ) = app & comp-sub-ren ξ η 𝒟 ⊗ comp-sub-ren ξ η ℰ


--------------------------------------------------------------------------------


id-cons-wk-sub : ∀ {Γ Ξ A B} → (ξ : Γ ⊢ Ξ alltrue) (𝒟 : Γ ⊢ A true) (ℰ : Ξ ⊢ B true)
                             → sub (ξ , 𝒟) (wk ℰ) ≡ sub ξ ℰ
id-cons-wk-sub ξ 𝒟 ℰ = comp-sub-ren (ξ , 𝒟) (drop id) ℰ ⁻¹
                     ⋮ (\ ξ′ → sub ξ′ ℰ) & id-gets ξ


id-cons-wks-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢ Ξ alltrue) (𝒟 : Γ ⊢ A true) (ψ : Ξ ⊢ Ψ alltrue)
                               → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
id-cons-wks-subs ξ 𝒟 ∙       = refl
id-cons-wks-subs ξ 𝒟 (ψ , ℰ) = _,_ & id-cons-wks-subs ξ 𝒟 ψ ⊗ id-cons-wk-sub ξ 𝒟 ℰ


--------------------------------------------------------------------------------


comp-ren-sub : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ alltrue) (𝒟 : Ξ ⊢ A true)
                            → sub (rens η ξ) 𝒟 ≡ (ren η ∘ sub ξ) 𝒟
comp-ren-sub η ξ (var i)   = comp-ren-get η ξ i
comp-ren-sub η ξ (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-rens η ξ ⁻¹
                                   ⋮ comp-ren-sub (keep η) (lifts ξ) 𝒟
                                   )
comp-ren-sub η ξ (app 𝒟 ℰ) = app & comp-ren-sub η ξ 𝒟 ⊗ comp-ren-sub η ξ ℰ


comp-rens-subs : ∀ {Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢ Ξ alltrue) (ψ : Ξ ⊢ Ψ alltrue)
                              → subs (rens η ξ) ψ ≡ (rens η ∘ subs ξ) ψ
comp-rens-subs η ξ ∙       = refl
comp-rens-subs η ξ (ψ , 𝒟) = _,_ & comp-rens-subs η ξ ψ ⊗ comp-ren-sub η ξ 𝒟


comp-lifts-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢ Ξ alltrue) (ψ : Ξ ⊢ Ψ alltrue)
                              → subs (lifts {A} ξ) (lifts ψ) ≡ (lifts ∘ subs ξ) ψ
comp-lifts-subs ξ ψ = (_, vz) & ( id-cons-wks-subs (wks ξ) vz ψ
                                ⋮ comp-rens-subs (drop id) ξ ψ
                                )


--------------------------------------------------------------------------------


id-sub : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → sub ids 𝒟 ≡ 𝒟
id-sub (var i)   = get-var i
id-sub (lam 𝒟)   = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ) = app & id-sub 𝒟 ⊗ id-sub ℰ


comp-sub : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢ Ξ alltrue) (ψ : Ξ ⊢ Ψ alltrue) (𝒟 : Ψ ⊢ A true)
                       → sub (subs ξ ψ) 𝒟 ≡ (sub ξ ∘ sub ψ) 𝒟
comp-sub ξ ψ (var i)   = comp-sub-get ξ ψ i
comp-sub ξ ψ (lam 𝒟)   = lam & ( (\ ξ′ → sub ξ′ 𝒟) & comp-lifts-subs ξ ψ ⁻¹
                               ⋮ comp-sub (lifts ξ) (lifts ψ) 𝒟
                               )
comp-sub ξ ψ (app 𝒟 ℰ) = app & comp-sub ξ ψ 𝒟 ⊗ comp-sub ξ ψ ℰ


lid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢ Ξ alltrue)
                   → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟


rid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢ Ξ alltrue)
                   → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( id-cons-wks-subs ξ 𝒟 ids
                            ⋮ rid-subs ξ
                            )


assoc-subs : ∀ {Γ Ξ Ψ Φ} → (ξ : Γ ⊢ Ξ alltrue) (ψ : Ξ ⊢ Ψ alltrue) (φ : Ψ ⊢ Φ alltrue)
                         → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ comp-sub ξ ψ 𝒟


instance
  𝐈𝐏𝐋 : Category (List Prop) _⊢_alltrue
  𝐈𝐏𝐋 = record
          { id     = ids
          ; _∘_    = flip subs
          ; lid∘   = rid-subs
          ; rid∘   = lid-subs
          ; assoc∘ = \ φ ψ ξ → assoc-subs ξ ψ φ ⁻¹
          }


𝐬𝐮𝐛 : ∀ {A} → Presheaf 𝐈𝐏𝐋 (_⊢ A true)
𝐬𝐮𝐛 = record
        { ℱ     = sub
        ; idℱ   = funext! id-sub
        ; compℱ = \ ψ ξ → funext! (comp-sub ξ ψ)
        }


--------------------------------------------------------------------------------
