module StdS4Lemmas where

open import Prelude
open import List
open import ListLemmas
open import StdS4


--------------------------------------------------------------------------------
{-

                lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)                    lookups-lookup
                   lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)                     rens-lookup
                      lookup (wks ξ) 𝒾 ≡ wk (lookup ξ 𝒾)                        wks-lookup
                          lookup ids 𝒾 ≡ var 𝒾                                  ids-lookup
                  lookup (mrens η ξ) 𝒾 ≡ mren η (lookup ξ 𝒾)                    mrens-lookup
                     lookup (mwks ξ) 𝒾 ≡ mwk (lookup ξ 𝒾)                       mwks-lookup
                 lookup (mrens₁ η ξ) 𝒾 ≡ mren η (lookup ξ 𝒾)                    mrens₁-lookup
                    lookup (mwks₁ ξ) 𝒾 ≡ mwk (lookup ξ 𝒾)                       mwks₁-lookup
                        lookup mids₁ 𝒾 ≡ mvar 𝒾                                 mids₁-lookup
                   lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)                     subs-lookup
                 lookup (msubs₁ ξ ψ) 𝒾 ≡ msub ξ (lookup ψ 𝒾)                    msubs₁-lookup

                         lookups ξ id⊇ ≡ ξ                                      id-lookups
                  lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁              comp-lookups
                lookups (rens η₁ ξ) η₂ ≡ rens η₁ (lookups ξ η₂)                 rens-lookups
                     lookups (wks ξ) η ≡ wks (lookups ξ η)                      wks-lookups
            lookups (lifts ξ) (keep η) ≡ lifts (lookups ξ η)                    lifts-lookups
                lookups (rens η ξ) id⊇ ≡ rens η ξ                               id-rens-lookups
                   lookups (wks ξ) id⊇ ≡ wks ξ                                  id-wks-lookups
          lookups (lifts ξ) (keep id⊇) ≡ lifts ξ                                id-lifts-lookups
               lookups (mrens η₁ ξ) η₂ ≡ mrens η₁ (lookups ξ η₂)                mrens-lookups
                    lookups (mwks ξ) η ≡ mwks (lookups ξ η)                     mwks-lookups
               lookups (mrens η ξ) id⊇ ≡ mrens η ξ                              id-mrens-lookups
                  lookups (mwks ξ) id⊇ ≡ mwks ξ                                 id-mwks-lookups
              lookups (mrens₁ η₁ ξ) η₂ ≡ mrens₁ η₁ (lookups ξ η₂)               mrens₁-lookups
                   lookups (mwks₁ ξ) η ≡ mwks₁ (lookups ξ η)                    mwks₁-lookups
          lookups (mlifts₁ ξ) (keep η) ≡ mlifts₁ (lookups ξ η)                  mlifts₁-lookups
                  lookups (subs ξ ψ) η ≡ subs ξ (lookups ψ η)                   subs-lookups
                lookups (msubs₁ ξ ψ) η ≡ msubs₁ ξ (lookups ψ η)                 msubs₁-lookups

                             ren id⊇ 𝒟 ≡ 𝒟                                      id-ren
                      ren (η₁ ∘⊇ η₂) 𝒟 ≡ ren η₂ (ren η₁ 𝒟)                      comp-ren

                            mren id⊇ 𝒟 ≡ 𝒟                                      id-mren
                     mren (η₁ ∘⊇ η₂) 𝒟 ≡ mren η₂ (mren η₁ 𝒟)                    comp-mren

                            rens id⊇ ξ ≡ ξ                                      id-rens
                     rens (η₁ ∘⊇ η₂) ξ ≡ rens η₂ (rens η₁ ξ)                    comp-rens
                       rens (drop η) ξ ≡ wks (rens η ξ)                         drop-wks-rens
                 rens (keep η) (wks ξ) ≡ wks (rens η ξ)                         keep-wks-rens
               rens (keep η) (lifts ξ) ≡ lifts (rens η ξ)                       keep-lifts-rens

                           mrens id⊇ ξ ≡ ξ                                      id-mrens
                    mrens (η₁ ∘⊇ η₂) ξ ≡ mrens η₂ (mrens η₁ ξ)                  comp-mrens
                      mrens (drop η) ξ ≡ mwks (mrens η ξ)                       drop-mwks-mrens
               mrens (keep η) (mwks ξ) ≡ mwks (mrens η ξ)                       keep-mwks-mrens

                          mrens₁ id⊇ ξ ≡ ξ                                      id-mrens₁
                   mrens₁ (η₁ ∘⊇ η₂) ξ ≡ mrens₁ η₂ (mrens₁ η₁ ξ)                comp-mrens₁
                     mrens₁ (drop η) ξ ≡ mwks₁ (mrens₁ η ξ)                     drop-mwks₁-mrens₁
             mrens₁ (keep η) (mwks₁ ξ) ≡ mwks₁ (mrens₁ η ξ)                     keep-mwks₁-mrens₁
           mrens₁ (keep η) (mlifts₁ ξ) ≡ mlifts₁ (mrens₁ η ξ)                   keep-mlifts₁-mrens₁

                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                      sub (mwks ids) 𝒟 ≡ 𝒟                                      id-mwks-sub
                   sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)                        lookups-sub
           sub (lifts (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (keep η) 𝒟)         lookups-lifts-sub
            sub (mwks (lookups ξ η)) 𝒟 ≡ sub (mwks ξ) (ren η 𝒟)                 lookups-mwks-sub
                      sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)                        rens-sub
              sub (lifts (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)         rens-lifts-sub
               sub (mwks (rens η ξ)) 𝒟 ≡ ren η (sub (mwks ξ) 𝒟)                 rens-mwks-sub

                  subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ                               absorb-subs
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                  subs (lookups ξ η) ψ ≡ subs ξ (rens η ψ)                      lookups-subs
                     subs (rens η ξ) ψ = rens η (subs ξ ψ)                      rens-subs
                        subs (wks ξ) ψ ≡ wks (subs ξ ψ)                         wks-subs
              subs (lifts ξ) (lifts ψ) ≡ lifts (subs ξ ψ)                       lifts-subs
                   subs (rens η ids) ξ ≡ rens η ξ                               lid-rens-subs
                   subs (rens η ξ) ids ≡ rens η ξ                               rid-rens-subs
                      subs (wks ids) ξ ≡ wks ξ                                  lid-wks-subs
                      subs (wks ξ) ids ≡ wks ξ                                  rid-wks-subs

                      sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟)                        subs-sub
              sub (lifts (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)        subs-lifts-sub
               sub (mwks (subs ξ ψ)) 𝒟 ≡ sub (mwks ξ) (sub (mwks ψ) 𝒟)          subs-mwks-sub

                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs

-}
--------------------------------------------------------------------------------


lookups-lookup : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒾 : Ξ ∋ A true)
                                → lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)
lookups-lookup ∙       done     ()
lookups-lookup (ξ , 𝒟) (drop η) 𝒾       = lookups-lookup ξ η 𝒾
lookups-lookup (ξ , 𝒟) (keep η) zero    = refl
lookups-lookup (ξ , 𝒟) (keep η) (suc 𝒾) = lookups-lookup ξ η 𝒾


rens-lookup : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                             → lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)
rens-lookup η (ξ , 𝒟) zero    = refl
rens-lookup η (ξ , 𝒟) (suc 𝒾) = rens-lookup η ξ 𝒾


wks-lookup : ∀ {Δ Γ Ξ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                           → lookup (wks {B} ξ) 𝒾 ≡ wk (lookup ξ 𝒾)
wks-lookup ξ 𝒾 = rens-lookup (drop id⊇) ξ 𝒾


ids-lookup : ∀ {Δ Γ A} → (𝒾 : Γ ∋ A true)
                       → lookup (ids {Δ = Δ}) 𝒾 ≡ var 𝒾
ids-lookup zero    = refl
ids-lookup (suc 𝒾) = wks-lookup ids 𝒾
                   ⋮ wk & ids-lookup 𝒾
                   ⋮ (\ 𝒾′ → var (suc 𝒾′)) & id-ren∋ 𝒾


mrens-lookup : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                              → lookup (mrens η ξ) 𝒾 ≡ mren η (lookup ξ 𝒾)
mrens-lookup η (ξ , 𝒟) zero    = refl
mrens-lookup η (ξ , 𝒟) (suc 𝒾) = mrens-lookup η ξ 𝒾


mwks-lookup : ∀ {Δ Γ Ξ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                            → lookup (mwks {B} ξ) 𝒾 ≡ mwk (lookup ξ 𝒾)
mwks-lookup ξ 𝒾 = mrens-lookup (drop id⊇) ξ 𝒾


mrens₁-lookup : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ) (𝒾 : Ξ ∋ A valid)
                             → lookup (mrens₁ η ξ) 𝒾 ≡ mren η (lookup ξ 𝒾)
mrens₁-lookup η (ξ , 𝒟) zero    = refl
mrens₁-lookup η (ξ , 𝒟) (suc 𝒾) = mrens₁-lookup η ξ 𝒾


mwks₁-lookup : ∀ {Δ Ξ A B} → (ξ : Δ ⊢⋆₁ Ξ) (𝒾 : Ξ ∋ A valid)
                           → lookup (mwks₁ {B} ξ) 𝒾 ≡ mwk (lookup ξ 𝒾)
mwks₁-lookup ξ 𝒾 = mrens₁-lookup (drop id⊇) ξ 𝒾


mids₁-lookup : ∀ {Δ A} → (𝒾 : Δ ∋ A valid)
                       → lookup mids₁ 𝒾 ≡ mvar 𝒾
mids₁-lookup zero    = refl
mids₁-lookup (suc 𝒾) = mwks₁-lookup mids₁ 𝒾
                     ⋮ mwk & mids₁-lookup 𝒾
                     ⋮ (\ 𝒾′ → mvar (suc 𝒾′)) & id-ren∋ 𝒾


subs-lookup : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                            → lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)
subs-lookup ξ (ψ , 𝒟) zero    = refl
subs-lookup ξ (ψ , ℰ) (suc 𝒾) = subs-lookup ξ ψ 𝒾


msubs₁-lookup : ∀ {Δ Ξ Ψ A} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ) (𝒾 : Ψ ∋ A valid)
                            → lookup (msubs₁ ξ ψ) 𝒾 ≡ msub ξ (lookup ψ 𝒾)
msubs₁-lookup ξ (ψ , 𝒟) zero    = refl
msubs₁-lookup ξ (ψ , ℰ) (suc 𝒾) = msubs₁-lookup ξ ψ 𝒾


--------------------------------------------------------------------------------


id-lookups : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                       → lookups ξ id⊇ ≡ ξ
id-lookups ∙       = refl
id-lookups (ξ , 𝒟) = (_, 𝒟) & id-lookups ξ


comp-lookups : ∀ {Δ Γ Ξ Ξ′ Ξ″} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                               → lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁
comp-lookups ∙       η₁        done      = refl
comp-lookups (ξ , 𝒟) η₁        (drop η₂) = comp-lookups ξ η₁ η₂
comp-lookups (ξ , 𝒟) (drop η₁) (keep η₂) = comp-lookups ξ η₁ η₂
comp-lookups (ξ , 𝒟) (keep η₁) (keep η₂) = (_, 𝒟) & comp-lookups ξ η₁ η₂


rens-lookups : ∀ {Δ Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                               → lookups (rens η₁ ξ) η₂ ≡ rens η₁ (lookups ξ η₂)
rens-lookups η₁ ∙       done      = refl
rens-lookups η₁ (ξ , 𝒟) (drop η₂) = rens-lookups η₁ ξ η₂
rens-lookups η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & rens-lookups η₁ ξ η₂


wks-lookups : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                             → lookups (wks {A} ξ) η ≡ wks (lookups ξ η)
wks-lookups ξ η = rens-lookups (drop id⊇) ξ η


lifts-lookups : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                               → lookups (lifts {A} ξ) (keep η) ≡ lifts (lookups ξ η)
lifts-lookups ξ η = (_, vz) & wks-lookups ξ η


id-rens-lookups : ∀ {Δ Γ Γ′ Ξ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                               → lookups (rens η ξ) id⊇ ≡ rens η ξ
id-rens-lookups η ξ = id-lookups (rens η ξ)


id-wks-lookups : ∀ {Δ Γ Ξ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → lookups (wks {A} ξ) id⊇ ≡ wks ξ
id-wks-lookups ξ = id-rens-lookups (drop id⊇) ξ


id-lifts-lookups : ∀ {Δ Γ Ξ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                               → lookups (lifts {A} ξ) (keep id⊇) ≡ lifts ξ
id-lifts-lookups ξ = (_, vz) & id-wks-lookups ξ


mrens-lookups : ∀ {Δ Δ′ Γ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                                → lookups (mrens η₁ ξ) η₂ ≡ mrens η₁ (lookups ξ η₂)
mrens-lookups η₁ ∙       done      = refl
mrens-lookups η₁ (ξ , 𝒟) (drop η₂) = mrens-lookups η₁ ξ η₂
mrens-lookups η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & mrens-lookups η₁ ξ η₂


mwks-lookups : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                              → lookups (mwks {A} ξ) η ≡ mwks (lookups ξ η)
mwks-lookups ξ η = mrens-lookups (drop id⊇) ξ η


id-mrens-lookups : ∀ {Δ Δ′ Γ Ξ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                → lookups (mrens η ξ) id⊇ ≡ mrens η ξ
id-mrens-lookups η ξ = id-lookups (mrens η ξ)


id-mwks-lookups : ∀ {Δ Γ Ξ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                              → lookups (mwks {A} ξ) id⊇ ≡ mwks ξ
id-mwks-lookups ξ = id-mrens-lookups (drop id⊇) ξ


mrens₁-lookups : ∀ {Δ Δ′ Ξ Ξ′} → (η₁ : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                               → lookups (mrens₁ η₁ ξ) η₂ ≡ mrens₁ η₁ (lookups ξ η₂)
mrens₁-lookups η₁ ∙       done      = refl
mrens₁-lookups η₁ (ξ , 𝒟) (drop η₂) = mrens₁-lookups η₁ ξ η₂
mrens₁-lookups η₁ (ξ , 𝒟) (keep η₂) = (_, mren η₁ 𝒟) & mrens₁-lookups η₁ ξ η₂


mwks₁-lookups : ∀ {Δ Ξ Ξ′ A} → (ξ : Δ ⊢⋆₁ Ξ′) (η : Ξ′ ⊇ Ξ)
                             → lookups (mwks₁ {A} ξ) η ≡ mwks₁ (lookups ξ η)
mwks₁-lookups ξ η = mrens₁-lookups (drop id⊇) ξ η


mlifts₁-lookups : ∀ {Δ Ξ Ξ′ A} → (ξ : Δ ⊢⋆₁ Ξ′) (η : Ξ′ ⊇ Ξ)
                               → lookups (mlifts₁ {A} ξ) (keep η) ≡ mlifts₁ (lookups ξ η)
mlifts₁-lookups ξ η = (_, mvz) & mwks₁-lookups ξ η


subs-lookups : ∀ {Δ Γ Ξ Ψ Ψ′} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
                              → lookups (subs ξ ψ) η ≡ subs ξ (lookups ψ η)
subs-lookups ξ ∙       done     = refl
subs-lookups ξ (ψ , 𝒟) (drop η) = subs-lookups ξ ψ η
subs-lookups ξ (ψ , 𝒟) (keep η) = (_, sub ξ 𝒟) & subs-lookups ξ ψ η


msubs₁-lookups : ∀ {Δ Ξ Ψ Ψ′} → (ξ : Δ ⊢⋆₁ Ξ) (ψ : Ξ ⊢⋆₁ Ψ′) (η : Ψ′ ⊇ Ψ)
                              → lookups (msubs₁ ξ ψ) η ≡ msubs₁ ξ (lookups ψ η)
msubs₁-lookups ξ ∙       done     = refl
msubs₁-lookups ξ (ψ , 𝒟) (drop η) = msubs₁-lookups ξ ψ η
msubs₁-lookups ξ (ψ , 𝒟) (keep η) = (_, msub ξ 𝒟) & msubs₁-lookups ξ ψ η


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
                           → ren (η₁ ∘⊇ η₂) 𝒟 ≡ ren η₂ (ren η₁ 𝒟)
comp-ren η₁ η₂ (var 𝒾)      = var & comp-ren∋ η₁ η₂ 𝒾
comp-ren η₁ η₂ (lam 𝒟)      = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ)    = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ
comp-ren η₁ η₂ (mvar 𝒾)     = refl
comp-ren η₁ η₂ (box 𝒟)      = refl
comp-ren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ


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
                            → mren (η₁ ∘⊇ η₂) 𝒟 ≡ mren η₂ (mren η₁ 𝒟)
comp-mren η₁ η₂ (var 𝒾)      = refl
comp-mren η₁ η₂ (lam 𝒟)      = lam & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (app 𝒟 ℰ)    = app & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren η₁ η₂ ℰ
comp-mren η₁ η₂ (mvar 𝒾)     = mvar & comp-ren∋ η₁ η₂ 𝒾
comp-mren η₁ η₂ (box 𝒟)      = box & comp-mren η₁ η₂ 𝒟
comp-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comp-mren η₁ η₂ 𝒟 ⊗ comp-mren (keep η₁) (keep η₂) ℰ


comm-ren-mren : ∀ {Δ Δ′ Γ Γ′ A} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                                → mren η₁ (ren η₂ 𝒟) ≡ ren η₂ (mren η₁ 𝒟)
comm-ren-mren η₁ η₂ (var 𝒾)      = refl
comm-ren-mren η₁ η₂ (lam 𝒟)      = lam & comm-ren-mren η₁ (keep η₂) 𝒟
comm-ren-mren η₁ η₂ (app 𝒟 ℰ)    = app & comm-ren-mren η₁ η₂ 𝒟 ⊗ comm-ren-mren η₁ η₂ ℰ
comm-ren-mren η₁ η₂ (mvar 𝒾)     = refl
comm-ren-mren η₁ η₂ (box 𝒟)      = refl
comm-ren-mren η₁ η₂ (letbox 𝒟 ℰ) = letbox & comm-ren-mren η₁ η₂ 𝒟 ⊗ comm-ren-mren (keep η₁) η₂ ℰ


--------------------------------------------------------------------------------


id-rens : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                    → rens id⊇ ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟


comp-rens : ∀ {Δ Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                            → rens (η₁ ∘⊇ η₂) ξ ≡ rens η₂ (rens η₁ ξ)
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟


drop-wks-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                               → rens (drop {A = A} η) ξ ≡ wks (rens η ξ)
drop-wks-rens η ∙       = refl
drop-wks-rens η (ξ , 𝒟) = _,_ & drop-wks-rens η ξ
                              ⊗ ( (\ η′ → ren (drop η′) 𝒟) & rid-∘⊇ η ⁻¹
                                ⋮ comp-ren η (drop id⊇) 𝒟
                                )


keep-wks-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                               → rens (keep {A = A} η) (wks ξ) ≡ wks (rens η ξ)
keep-wks-rens η ∙       = refl
keep-wks-rens η (ξ , 𝒟) = _,_ & keep-wks-rens η ξ
                              ⊗ ( comp-ren (drop id⊇) (keep η) 𝒟 ⁻¹
                                ⋮ (\ η′ → ren (drop η′) 𝒟) & (lid-∘⊇ η ⋮ rid-∘⊇ η ⁻¹)
                                ⋮ comp-ren η (drop id⊇) 𝒟
                                )


keep-lifts-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                 → rens (keep {A = A} η) (lifts ξ) ≡ lifts (rens η ξ)
keep-lifts-rens η ξ = (_, vz) & keep-wks-rens η ξ


--------------------------------------------------------------------------------


id-mrens : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → mrens id⊇ ξ ≡ ξ
id-mrens ∙       = refl
id-mrens (ξ , 𝒟) = _,_ & id-mrens ξ ⊗ id-mren 𝒟


comp-mrens : ∀ {Δ Δ′ Δ″ Γ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → mrens (η₁ ∘⊇ η₂) ξ ≡ mrens η₂ (mrens η₁ ξ)
comp-mrens η₁ η₂ ∙       = refl
comp-mrens η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens η₁ η₂ ξ ⊗ comp-mren η₁ η₂ 𝒟


drop-mwks-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                 → mrens (drop {A = A} η) ξ ≡ mwks (mrens η ξ)
drop-mwks-mrens η ∙       = refl
drop-mwks-mrens η (ξ , 𝒟) = _,_ & drop-mwks-mrens η ξ
                                ⊗ ( (\ η′ → mren (drop η′) 𝒟) & rid-∘⊇ η ⁻¹
                                  ⋮ comp-mren η (drop id⊇) 𝒟
                                  )


keep-mwks-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                                 → mrens (keep {A = A} η) (mwks ξ) ≡ mwks (mrens η ξ)
keep-mwks-mrens η ∙       = refl
keep-mwks-mrens η (ξ , 𝒟) = _,_ & keep-mwks-mrens η ξ
                                ⊗ ( comp-mren (drop id⊇) (keep η) 𝒟 ⁻¹
                                  ⋮ (\ η′ → mren (drop η′) 𝒟) & (lid-∘⊇ η ⋮ rid-∘⊇ η ⁻¹)
                                  ⋮ comp-mren η (drop id⊇) 𝒟
                                  )


--------------------------------------------------------------------------------


id-mrens₁ : ∀ {Δ Ξ} → (ξ : Δ ⊢⋆₁ Ξ)
                    → mrens₁ id⊇ ξ ≡ ξ
id-mrens₁ ∙       = refl
id-mrens₁ (ξ , 𝒟) = _,_ & id-mrens₁ ξ ⊗ id-mren 𝒟


comp-mrens₁ : ∀ {Δ Δ′ Δ″ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Δ″ ⊇ Δ′) (ξ : Δ ⊢⋆₁ Ξ)
                            → mrens₁ (η₁ ∘⊇ η₂) ξ ≡ mrens₁ η₂ (mrens₁ η₁ ξ)
comp-mrens₁ η₁ η₂ ∙       = refl
comp-mrens₁ η₁ η₂ (ξ , 𝒟) = _,_ & comp-mrens₁ η₁ η₂ ξ ⊗ comp-mren η₁ η₂ 𝒟


drop-mwks₁-mrens₁ : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                 → mrens₁ (drop {A = A} η) ξ ≡ mwks₁ (mrens₁ η ξ)
drop-mwks₁-mrens₁ η ∙       = refl
drop-mwks₁-mrens₁ η (ξ , 𝒟) = _,_ & drop-mwks₁-mrens₁ η ξ
                                  ⊗ ( (\ η′ → mren (drop η′) 𝒟) & rid-∘⊇ η ⁻¹
                                    ⋮ comp-mren η (drop id⊇) 𝒟
                                    )


keep-mwks₁-mrens₁ : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                 → mrens₁ (keep {A = A} η) (mwks₁ ξ) ≡ mwks₁ (mrens₁ η ξ)
keep-mwks₁-mrens₁ η ∙       = refl
keep-mwks₁-mrens₁ η (ξ , 𝒟) = _,_ & keep-mwks₁-mrens₁ η ξ
                                  ⊗ ( comp-mren (drop id⊇) (keep η) 𝒟 ⁻¹
                                    ⋮ (\ η′ → mren (drop η′) 𝒟) & (lid-∘⊇ η ⋮ rid-∘⊇ η ⁻¹)
                                    ⋮ comp-mren η (drop id⊇) 𝒟
                                    )


keep-mlifts₁-mrens₁ : ∀ {Δ Δ′ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⊢⋆₁ Ξ)
                                   → mrens₁ (keep {A = A} η) (mlifts₁ ξ) ≡ mlifts₁ (mrens₁ η ξ)
keep-mlifts₁-mrens₁ η ξ = (_, mvz) & keep-mwks₁-mrens₁ η ξ


--------------------------------------------------------------------------------


mrens-rens : ∀ {Δ Δ′ Γ Γ′ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → rens η₂ (mrens η₁ ξ) ≡ mrens η₁ (rens η₂ ξ)
mrens-rens η₁ η₂ ∙       = refl
mrens-rens η₁ η₂ (ξ , 𝒟) = _,_ & mrens-rens η₁ η₂ ξ ⊗ comm-ren-mren η₁ η₂ 𝒟 ⁻¹

mwks-rens : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                           → rens η (mwks ξ) ≡ mwks {A} (rens η ξ)
mwks-rens η ξ = mrens-rens (drop id⊇) η ξ


rens-mrens : ∀ {Δ Δ′ Γ Γ′ Ξ} → (η₁ : Δ′ ⊇ Δ) (η₂ : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → mrens η₁ (rens η₂ ξ) ≡ rens η₂ (mrens η₁ ξ)
rens-mrens η₁ η₂ ξ = mrens-rens η₁ η₂ ξ ⁻¹

wks-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                           → mrens η (wks ξ) ≡ wks {A} (mrens η ξ)
wks-mrens η ξ = rens-mrens η (drop id⊇) ξ

lifts-mrens : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → mrens η (lifts ξ) ≡ lifts {A} (mrens η ξ)
lifts-mrens η ξ = (_, vz) & wks-mrens η ξ


mren-lookup : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                             → lookup (mrens η ξ) 𝒾 ≡ mren η (lookup ξ 𝒾)
mren-lookup η (ξ , 𝒟) zero    = refl
mren-lookup η (ξ , ℰ) (suc 𝒾) = mren-lookup η ξ 𝒾


mutual
  mren-sub : ∀ {Δ Δ′ Γ Ξ A} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                            → sub (mrens η ξ) (mren η 𝒟) ≡ mren η (sub ξ 𝒟)
  mren-sub η ξ (var 𝒾)      = mren-lookup η ξ 𝒾
  mren-sub η ξ (lam 𝒟)      = lam & mren-lifts-sub η ξ 𝒟
  mren-sub η ξ (app 𝒟 ℰ)    = app & mren-sub η ξ 𝒟 ⊗ mren-sub η ξ ℰ
  mren-sub η ξ (mvar 𝒾)     = refl
  mren-sub η ξ (box 𝒟)      = refl
  mren-sub η ξ (letbox 𝒟 ℰ) = letbox & mren-sub η ξ 𝒟 ⊗ mren-mwks-sub η ξ ℰ

  mren-lifts-sub : ∀ {Δ Δ′ Γ Ξ A B} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ , B true ⊢ A true)
                                    → sub (lifts {B} (mrens η ξ)) (mren η 𝒟) ≡ mren η (sub (lifts ξ) 𝒟)
  mren-lifts-sub η ξ 𝒟 = (\ ξ′ → sub ξ′ (mren η 𝒟)) & lifts-mrens η ξ ⁻¹
                       ⋮ mren-sub η (lifts ξ) 𝒟

  mren-mwks-sub : ∀ {Δ Δ′ Γ Ξ A B} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ , B valid ⨾ Ξ ⊢ A true)
                                   → sub (mwks {B} (mrens η ξ)) (mren (keep η) 𝒟) ≡ mren (keep η) (sub (mwks ξ) 𝒟)
  mren-mwks-sub η ξ 𝒟 = (\ ξ′ → sub ξ′ (mren (keep η) 𝒟)) & keep-mwks-mrens η ξ ⁻¹
                      ⋮ mren-sub (keep η) (mwks ξ) 𝒟


mrens-subs : ∀ {Δ Δ′ Γ Ξ Ψ} → (η : Δ′ ⊇ Δ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                            → subs (mrens η ξ) (mrens η ψ) ≡ mrens η (subs ξ ψ)
mrens-subs η ξ ∙       = refl
mrens-subs η ξ (ψ , 𝒟) = _,_ & mrens-subs η ξ ψ ⊗ mren-sub η ξ 𝒟

mwks-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                          → subs (mwks {A} ξ) (mwks {A} ψ) ≡ mwks (subs ξ ψ)
mwks-subs ξ ψ = mrens-subs (drop id⊇) ξ ψ


--------------------------------------------------------------------------------


id-mrens-sub : ∀ {Δ Δ′ Γ A} → (η : Δ′ ⊇ Δ) (𝒟 : Δ′ ⨾ Γ ⊢ A true)
                            → sub (mrens η ids) 𝒟 ≡ 𝒟
id-mrens-sub η (var 𝒾)      = mrens-lookup η ids 𝒾
                            ⋮ mren η & ids-lookup 𝒾
id-mrens-sub η (lam 𝒟)      = lam & ( (\ ξ′ → sub ξ′ 𝒟) & lifts-mrens η ids ⁻¹
                                    ⋮ id-mrens-sub η 𝒟
                                    )
id-mrens-sub η (app 𝒟 ℰ)    = app & id-mrens-sub η 𝒟 ⊗ id-mrens-sub η ℰ
id-mrens-sub η (mvar 𝒾)     = refl
id-mrens-sub η (box 𝒟)      = refl
id-mrens-sub η (letbox 𝒟 ℰ) = letbox & id-mrens-sub η 𝒟
                                     ⊗ ( (\ ξ′ → sub ξ′ ℰ) & drop-mwks-mrens η ids ⁻¹
                                       ⋮ id-mrens-sub (drop η) ℰ
                                       )


id-sub : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                   → sub ids 𝒟 ≡ 𝒟
id-sub (var 𝒾)      = ids-lookup 𝒾
id-sub (lam 𝒟)      = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ)    = app & id-sub 𝒟 ⊗ id-sub ℰ
id-sub (mvar 𝒾)     = refl
id-sub (box 𝒟)      = refl
id-sub (letbox 𝒟 ℰ) = letbox & id-sub 𝒟 ⊗ id-mrens-sub (drop id⊇) ℰ


mutual
  lookups-sub : ∀ {Δ Γ Ξ Ξ′ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                               → sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)
  lookups-sub ξ η (var 𝒾)      = lookups-lookup ξ η 𝒾
  lookups-sub ξ η (lam 𝒟)      = lam & lookups-lifts-sub ξ η 𝒟
  lookups-sub ξ η (app 𝒟 ℰ)    = app & lookups-sub ξ η 𝒟 ⊗ lookups-sub ξ η ℰ
  lookups-sub ξ η (mvar 𝒾)     = refl
  lookups-sub ξ η (box 𝒟)      = refl
  lookups-sub ξ η (letbox 𝒟 ℰ) = letbox & lookups-sub ξ η 𝒟 ⊗ lookups-mwks-sub ξ η ℰ

  lookups-lifts-sub : ∀ {Δ Γ Ξ Ξ′ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Δ ⨾ Ξ , B true ⊢ A true)
                                       → sub (lifts {B} (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (keep η) 𝒟)
  lookups-lifts-sub ξ η 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & lifts-lookups ξ η ⁻¹
                          ⋮ lookups-sub (lifts ξ) (keep η) 𝒟

  lookups-mwks-sub : ∀ {Δ Γ Ξ Ξ′ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Δ , B valid ⨾ Ξ ⊢ A true)
                                      → sub (mwks {B} (lookups ξ η)) 𝒟 ≡ sub (mwks ξ) (ren η 𝒟)
  lookups-mwks-sub ξ η 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & mwks-lookups ξ η ⁻¹
                         ⋮ lookups-sub (mwks ξ) η 𝒟


mutual
  rens-sub : ∀ {Δ Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ ⊢ A true)
                            → sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)
  rens-sub η ξ (var 𝒾)      = rens-lookup η ξ 𝒾
  rens-sub η ξ (lam 𝒟)      = lam & rens-lifts-sub η ξ 𝒟
  rens-sub η ξ (app 𝒟 ℰ)    = app & rens-sub η ξ 𝒟 ⊗ rens-sub η ξ ℰ
  rens-sub η ξ (mvar 𝒾)     = refl
  rens-sub η ξ (box 𝒟)      = refl
  rens-sub η ξ (letbox 𝒟 ℰ) = letbox & rens-sub η ξ 𝒟 ⊗ rens-mwks-sub η ξ ℰ

  rens-lifts-sub : ∀ {Δ Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ ⨾ Ξ , B true ⊢ A true)
                                    → sub (lifts {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)
  rens-lifts-sub η ξ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & keep-lifts-rens η ξ ⁻¹
                       ⋮ rens-sub (keep η) (lifts ξ) 𝒟

  rens-mwks-sub : ∀ {Δ Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (𝒟 : Δ , B valid ⨾ Ξ ⊢ A true)
                                   → sub (mwks {B} (rens η ξ)) 𝒟 ≡ ren η (sub (mwks ξ) 𝒟)
  rens-mwks-sub η ξ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & mwks-rens η ξ ⁻¹
                      ⋮ rens-sub η (mwks ξ) 𝒟


--------------------------------------------------------------------------------


absorb-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ ⨾ Γ ⊢ A true)
                            → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
absorb-subs ξ ∙       𝒟 = refl
absorb-subs ξ (ψ , ℰ) 𝒟 = _,_ & absorb-subs ξ ψ 𝒟
                              ⊗ ( lookups-sub (ξ , 𝒟) (drop id⊇) ℰ ⁻¹
                                ⋮ (\ ξ′ → sub ξ′ ℰ) & id-lookups ξ
                                )


lid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟


rid-subs : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                     → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( absorb-subs ξ ids 𝒟
                            ⋮ rid-subs ξ
                            )


lookups-subs : ∀ {Δ Γ Ξ Ξ′ Ψ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                              → subs (lookups ξ η) ψ ≡ subs ξ (rens η ψ)
lookups-subs ξ η ∙       = refl
lookups-subs ξ η (ψ , 𝒟) = _,_ & lookups-subs ξ η ψ ⊗ lookups-sub ξ η 𝒟


rens-subs : ∀ {Δ Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                           → subs (rens η ξ) ψ ≡ rens η (subs ξ ψ)
rens-subs η ξ ∙       = refl
rens-subs η ξ (ψ , 𝒟) = _,_ & rens-subs η ξ ψ ⊗ rens-sub η ξ 𝒟


wks-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                         → subs (wks {A} ξ) ψ ≡ wks (subs ξ ψ)
wks-subs ξ ψ = rens-subs (drop id⊇) ξ ψ


lifts-subs : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ)
                           → subs (lifts {A} ξ) (lifts ψ) ≡ lifts (subs ξ ψ)
lifts-subs ξ ψ = (_, vz) & ( absorb-subs (wks ξ) ψ vz
                           ⋮ wks-subs ξ ψ
                           )


lid-rens-subs : ∀ {Δ Γ Γ′ Ξ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → subs (rens η ids) ξ ≡ rens η ξ
lid-rens-subs η ξ = rens-subs η ids ξ ⋮ (rens η & lid-subs ξ)


rid-rens-subs : ∀ {Δ Γ Γ′ Ξ} → (η : Γ′ ⊇ Γ) (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                             → subs (rens η ξ) ids ≡ rens η ξ
rid-rens-subs η ξ = rens-subs η ξ ids ⋮ (rens η & rid-subs ξ)


lid-wks-subs : ∀ {Δ Γ Ξ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                           → subs (wks {A} ids) ξ ≡ wks ξ
lid-wks-subs ξ = lid-rens-subs (drop id⊇) ξ


rid-wks-subs : ∀ {Δ Γ Ξ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ)
                           → subs (wks {A} ξ) ids ≡ wks ξ
rid-wks-subs ξ = rid-rens-subs (drop id⊇) ξ


--------------------------------------------------------------------------------


mutual
  subs-sub : ∀ {Δ Γ Ξ Ψ A} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ ⨾ Ψ ⊢ A true)
                           → sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟)
  subs-sub ξ ψ (var 𝒾)      = subs-lookup ξ ψ 𝒾
  subs-sub ξ ψ (lam 𝒟)      = lam & subs-lifts-sub ξ ψ 𝒟
  subs-sub ξ ψ (app 𝒟 ℰ)    = app & subs-sub ξ ψ 𝒟 ⊗ subs-sub ξ ψ ℰ
  subs-sub ξ ψ (mvar 𝒾)     = refl
  subs-sub ξ ψ (box 𝒟)      = refl
  subs-sub ξ ψ (letbox 𝒟 ℰ) = letbox & subs-sub ξ ψ 𝒟 ⊗ subs-mwks-sub ξ ψ ℰ

  subs-lifts-sub : ∀ {Δ Γ Ξ Ψ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ ⨾ Ψ , B true ⊢ A true)
                                   → sub (lifts {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)
  subs-lifts-sub ξ ψ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & lifts-subs ξ ψ ⁻¹
                       ⋮ subs-sub (lifts ξ) (lifts ψ) 𝒟

  subs-mwks-sub : ∀ {Δ Γ Ξ Ψ A B} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (𝒟 : Δ , B valid ⨾ Ψ ⊢ A true)
                                  → sub (mwks {B} (subs ξ ψ)) 𝒟 ≡ sub (mwks ξ) (sub (mwks ψ) 𝒟)
  subs-mwks-sub ξ ψ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & mwks-subs ξ ψ ⁻¹
                      ⋮ subs-sub (mwks ξ) (mwks ψ) 𝒟


--------------------------------------------------------------------------------


assoc-subs : ∀ {Δ Γ Ξ Ψ Φ} → (ξ : Δ ⨾ Γ ⊢⋆ Ξ) (ψ : Δ ⨾ Ξ ⊢⋆ Ψ) (φ : Δ ⨾ Ψ ⊢⋆ Φ)
                           → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ subs-sub ξ ψ 𝒟


--------------------------------------------------------------------------------
