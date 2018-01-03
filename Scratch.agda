
{-
renamings on terms

_∋⋆_       -- _≥_
putᵣ       -- (not needed)
getᵣ       -- renFin
wkᵣ        -- drop
liftᵣ      -- keep
idᵣ        -- id≥
ren        -- REN, MREN
wk         -- WK, MWK
_○_        -- _∘≥_

natgetᵣ    -- (not needed)
idgetᵣ     -- idrenFin
idren      -- idREN, idMREN

zap○       -- (not clear)
lid○       -- lid∘≥
rid○       -- rid∘≥

get○       -- assocrenFin
wk○        -- (not needed)
lift○      -- (not needed)
wklid○     -- ...
wkrid○     -- ...
liftwkrid○ -- ...
ren○       -- assocREN, assocMREN
renlift○   -- (easy from assocREN)
renwk○     -- ...
renliftwk○ -- ...

assoc○     -- assoc∘≥

(not here) -- commRENMREN




substitutions on terms

_⊢⋆_      -- Terms
putₛ       -- (not needed)
getₛ       -- get
wkₛ        -- WKS
liftₛ      -- LIFTS
idₛ        -- IDS
sub        -- SUB
cut        -- CUT
_●_        -- SUBS

natgetₛ    -- getWKS
idgetₛ     -- getIDS
idsub      -- idSUB

⌊_⌋        -- HYPS, MHYPS₁
_◐_        -- gets
_◑_        -- RENS, MRENS
⌊get⌋      -- ...
⌊wk⌋       -- ...
⌊lift⌋     -- ...
⌊id⌋       -- ...
⌊sub⌋      -- ...
⌊○⌋        -- ...

zap◐
rid◐

get◐
wk◐
lift◐
wkrid◐
litwkrid◐
sub◐
sublift◐
subwk◐
subliftwk◐ --

zap◑
lid◑       -- idRENS

zap●
lid●
rid●

get◑
wk◑
lift◑
wklid◑
liftwklid◑
sub◑
sublift◑
subwk◑
subliftwk◑

get●
wk●
lift●
wklid●
wkrid●
liftwkrid●
sub●
sublift●
subwk●
subliftwk●

comp◐○
comp◑○
comp◑◐
comp◑●
comp●◐
comp●◑

assoc●
-}

open import Prelude
open import List
open import ListLemmas
open import StdIPL


--------------------------------------------------------------------------------
{-
                                                                              
                lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)                    lookups-lookup
                   lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)                     rens-lookup
                      lookup (wks ξ) 𝒾 ≡ wk (lookup ξ 𝒾)                        wks-lookup
                          lookup ids 𝒾 ≡ var 𝒾                                  ids-lookup
                   lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)                     subs-lookup
         
                         lookups ξ id⊇ ≡ ξ                                      id-lookups
                  lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁              comp-lookups
                lookups (rens η₁ ξ) η₂ ≡ rens η₁ (lookups ξ η₂)                 rens-lookups
                     lookups (wks ξ) η ≡ wks (lookups ξ η)                      wks-lookups
            lookups (lifts ξ) (keep η) ≡ lifts (lookups ξ η)                    lifts-lookups
                  lookups (subs ξ ψ) η ≡ subs ξ (lookups ψ η)                   subs-lookups
         
                             ren id⊇ 𝒟 ≡ 𝒟                                      id-ren
                      ren (η₁ ∘⊇ η₂) 𝒟 ≡ ren η₂ (ren η₁ 𝒟)                      comp-ren
         
                            rens id⊇ ξ ≡ ξ                                      id-rens
                     rens (η₁ ∘⊇ η₂) ξ ≡ rens η₂ (rens η₁ ξ)                    comp-rens
                       rens (drop η) ξ ≡ wks (rens η ξ)                         drop-wks-rens
                 rens (keep η) (wks ξ) ≡ wks (rens η ξ)                         keep-wks-rens
               rens (keep η) (lifts ξ) ≡ lifts (rens η ξ)                       keep-lifts-rens
         
                             sub ids 𝒟 ≡ 𝒟                                      id-sub
                   sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)                        lookups-sub
           sub (lifts (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (keep η) 𝒟)         lookups-lifts-sub
                      sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)                        rens-sub
              sub (lifts (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)         rens-lifts-sub
         
                  subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ                               absorb-subs
                            subs ids ξ ≡ ξ                                      lid-subs
                            subs ξ ids ≡ ξ                                      rid-subs
                  subs (lookups ξ η) ψ ≡ subs ξ (rens η ψ)                      lookups-subs
                     subs (rens η ξ) ψ = rens η (subs ξ ψ)                      rens-subs
                        subs (wks ξ) ψ ≡ wks (subs ξ ψ)                         wks-subs
              subs (lifts ξ) (lifts ψ) ≡ lifts (subs ξ ψ)                       lifts-subs
         
                      sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟)                        subs-sub
              sub (lifts (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)        subs-lifts-sub
         
                     subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)                      assoc-subs

-}
--------------------------------------------------------------------------------


lookups-lookup : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒾 : Ξ ∋ A true)
                              → lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)
lookups-lookup ∙       done     ()
lookups-lookup (ξ , 𝒟) (drop η) 𝒾       = lookups-lookup ξ η 𝒾
lookups-lookup (ξ , 𝒟) (keep η) zero    = refl
lookups-lookup (ξ , 𝒟) (keep η) (suc 𝒾) = lookups-lookup ξ η 𝒾

rens-lookup : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                           → lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)
rens-lookup η (ξ , 𝒟) zero    = refl
rens-lookup η (ξ , 𝒟) (suc 𝒾) = rens-lookup η ξ 𝒾

wks-lookup : ∀ {Γ Ξ A B} → (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                         → lookup (wks {B} ξ) 𝒾 ≡ wk (lookup ξ 𝒾)
wks-lookup ξ 𝒾 = rens-lookup (drop id⊇) ξ 𝒾

ids-lookup : ∀ {Γ A} → (𝒾 : Γ ∋ A true)
                     → lookup ids 𝒾 ≡ var 𝒾
ids-lookup zero    = refl
ids-lookup (suc 𝒾) = wks-lookup ids 𝒾
                   ⦙ wk & ids-lookup 𝒾
                   ⦙ (\ 𝒾′ → var (suc 𝒾′)) & id-ren∋ 𝒾 

subs-lookup : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                          → lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)
subs-lookup ξ (ψ , 𝒟) zero    = refl
subs-lookup ξ (ψ , ℰ) (suc 𝒾) = subs-lookup ξ ψ 𝒾

--------------------------------------------------------------------------------

id-lookups : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                     → lookups ξ id⊇ ≡ ξ
id-lookups ∙       = refl
id-lookups (ξ , 𝒟) = (_, 𝒟) & id-lookups ξ

comp-lookups : ∀ {Γ Ξ Ξ′ Ξ″} → (ξ : Γ ⊢⋆ Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                             → lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁
comp-lookups ∙       η₁        done      = refl
comp-lookups (ξ , 𝒟) η₁        (drop η₂) = comp-lookups ξ η₁ η₂
comp-lookups (ξ , 𝒟) (drop η₁) (keep η₂) = comp-lookups ξ η₁ η₂
comp-lookups (ξ , 𝒟) (keep η₁) (keep η₂) = (_, 𝒟) & comp-lookups ξ η₁ η₂

rens-lookups : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                             → lookups (rens η₁ ξ) η₂ ≡ rens η₁ (lookups ξ η₂)
rens-lookups η₁ ∙       done      = refl
rens-lookups η₁ (ξ , 𝒟) (drop η₂) = rens-lookups η₁ ξ η₂
rens-lookups η₁ (ξ , 𝒟) (keep η₂) = (_, ren η₁ 𝒟) & rens-lookups η₁ ξ η₂

wks-lookups : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                           → lookups (wks {A} ξ) η ≡ wks (lookups ξ η)
wks-lookups ξ η = rens-lookups (drop id⊇) ξ η

lifts-lookups : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                             → lookups (lifts {A} ξ) (keep η) ≡ lifts (lookups ξ η)
lifts-lookups ξ η = (_, vz) & wks-lookups ξ η

subs-lookups : ∀ {Γ Ξ Ψ Ψ′} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
                            → lookups (subs ξ ψ) η ≡ subs ξ (lookups ψ η)
subs-lookups ξ ∙       done     = refl
subs-lookups ξ (ψ , 𝒟) (drop η) = subs-lookups ξ ψ η
subs-lookups ξ (ψ , 𝒟) (keep η) = (_, sub ξ 𝒟) & subs-lookups ξ ψ η

--------------------------------------------------------------------------------

id-ren : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → ren id⊇ 𝒟 ≡ 𝒟
id-ren (var 𝒾)   = var & id-ren∋ 𝒾
id-ren (lam 𝒟)   = lam & id-ren 𝒟
id-ren (app 𝒟 ℰ) = app & id-ren 𝒟 ⊗ id-ren ℰ

comp-ren : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒟 : Γ ⊢ A true)
                         → ren (η₁ ∘⊇ η₂) 𝒟 ≡ ren η₂ (ren η₁ 𝒟)
comp-ren η₁ η₂ (var 𝒾)   = var & comp-ren∋ η₁ η₂ 𝒾 
comp-ren η₁ η₂ (lam 𝒟)   = lam & comp-ren (keep η₁) (keep η₂) 𝒟
comp-ren η₁ η₂ (app 𝒟 ℰ) = app & comp-ren η₁ η₂ 𝒟 ⊗ comp-ren η₁ η₂ ℰ

--------------------------------------------------------------------------------

id-rens : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                  → rens id⊇ ξ ≡ ξ
id-rens ∙       = refl
id-rens (ξ , 𝒟) = _,_ & id-rens ξ ⊗ id-ren 𝒟

comp-rens : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Γ ⊢⋆ Ξ)
                          → rens (η₁ ∘⊇ η₂) ξ ≡ rens η₂ (rens η₁ ξ)
comp-rens η₁ η₂ ∙       = refl
comp-rens η₁ η₂ (ξ , 𝒟) = _,_ & comp-rens η₁ η₂ ξ ⊗ comp-ren η₁ η₂ 𝒟

drop-wks-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                             → rens (drop η) ξ ≡ wks {A} (rens η ξ)
drop-wks-rens η ∙       = refl
drop-wks-rens η (ξ , 𝒟) = _,_ & drop-wks-rens η ξ ⊗ ( (\ η′ → ren (drop η′) 𝒟) & rid-∘⊇ η ⁻¹
                                                    ⦙ comp-ren η (drop id⊇) 𝒟
                                                    )

keep-wks-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                             → rens (keep η) (wks ξ) ≡ wks {A} (rens η ξ)
keep-wks-rens η ∙       = refl
keep-wks-rens η (ξ , 𝒟) = _,_ & keep-wks-rens η ξ ⊗ ( comp-ren (drop id⊇) (keep η) 𝒟 ⁻¹
                                                    ⦙ (\ η′ → ren (drop η′) 𝒟) & (lid-∘⊇ η ⦙ rid-∘⊇ η ⁻¹)
                                                    ⦙ comp-ren η (drop id⊇) 𝒟 
                                                    )

keep-lifts-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                               → rens (keep η) (lifts ξ) ≡ lifts {A} (rens η ξ)
keep-lifts-rens η ξ = (_, vz) & keep-wks-rens η ξ

--------------------------------------------------------------------------------

id-sub : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
                 → sub ids 𝒟 ≡ 𝒟
id-sub (var 𝒾)   = ids-lookup 𝒾 
id-sub (lam 𝒟)   = lam & id-sub 𝒟
id-sub (app 𝒟 ℰ) = app & id-sub 𝒟 ⊗ id-sub ℰ

mutual
  lookups-sub : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                            → sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)
  lookups-sub ξ η (var 𝒾)   = lookups-lookup ξ η 𝒾
  lookups-sub ξ η (lam 𝒟)   = lam & lookups-lifts-sub ξ η 𝒟
  lookups-sub ξ η (app 𝒟 ℰ) = app & lookups-sub ξ η 𝒟 ⊗ lookups-sub ξ η ℰ

  lookups-lifts-sub : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                                     → sub (lifts (lookups ξ η)) 𝒟 ≡ sub (lifts {B} ξ) (ren (keep η) 𝒟)
  lookups-lifts-sub ξ η 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & lifts-lookups ξ η ⁻¹
                          ⦙ lookups-sub (lifts ξ) (keep η) 𝒟

mutual
  rens-sub : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)
  rens-sub η ξ (var 𝒾)   = rens-lookup η ξ 𝒾
  rens-sub η ξ (lam 𝒟)   = lam & rens-lifts-sub η ξ 𝒟
  rens-sub η ξ (app 𝒟 ℰ) = app & rens-sub η ξ 𝒟 ⊗ rens-sub η ξ ℰ

  rens-lifts-sub : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                                  → sub (lifts {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)
  rens-lifts-sub η ξ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & keep-lifts-rens η ξ ⁻¹
                       ⦙ rens-sub (keep η) (lifts ξ) 𝒟

--------------------------------------------------------------------------------

absorb-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Γ ⊢ A true)
                          → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
absorb-subs ξ ∙       𝒟 = refl
absorb-subs ξ (ψ , ℰ) 𝒟 = _,_ & absorb-subs ξ ψ 𝒟 ⊗ ( lookups-sub (ξ , 𝒟) (drop id⊇) ℰ ⁻¹
                                                    ⦙ (\ ξ′ → sub ξ′ ℰ) & id-lookups ξ
                                                    )

lid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                   → subs ids ξ ≡ ξ
lid-subs ∙       = refl
lid-subs (ξ , 𝒟) = _,_ & lid-subs ξ ⊗ id-sub 𝒟

rid-subs : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
                   → subs ξ ids ≡ ξ
rid-subs ∙       = refl
rid-subs (ξ , 𝒟) = (_, 𝒟) & ( absorb-subs ξ ids 𝒟
                            ⦙ rid-subs ξ
                            )

lookups-subs : ∀ {Γ Ξ Ξ′ Ψ} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                            → subs (lookups ξ η) ψ ≡ subs ξ (rens η ψ)
lookups-subs ξ η ∙       = refl
lookups-subs ξ η (ψ , 𝒟) = _,_ & lookups-subs ξ η ψ ⊗ lookups-sub ξ η 𝒟

rens-subs : ∀ {Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                         → subs (rens η ξ) ψ ≡ rens η (subs ξ ψ)
rens-subs η ξ ∙       = refl
rens-subs η ξ (ψ , 𝒟) = _,_ & rens-subs η ξ ψ ⊗ rens-sub η ξ 𝒟 

wks-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                       → subs (wks {A} ξ) ψ ≡ wks (subs ξ ψ)
wks-subs ξ ψ = rens-subs (drop id⊇) ξ ψ

lifts-subs : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                         → subs (lifts {A} ξ) (lifts ψ) ≡ lifts (subs ξ ψ)
lifts-subs ξ ψ = (_, vz) & ( absorb-subs (wks ξ) ψ vz 
                           ⦙ wks-subs ξ ψ
                           )

--------------------------------------------------------------------------------

mutual
  subs-sub : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                         → sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟) 
  subs-sub ξ ψ (var 𝒾)   = subs-lookup ξ ψ 𝒾
  subs-sub ξ ψ (lam 𝒟)   = lam & subs-lifts-sub ξ ψ 𝒟
  subs-sub ξ ψ (app 𝒟 ℰ) = app & subs-sub ξ ψ 𝒟 ⊗ subs-sub ξ ψ ℰ

  subs-lifts-sub : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ , B true ⊢ A true)
                                 → sub (lifts {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)
  subs-lifts-sub ξ ψ 𝒟 = (\ ξ′ → sub ξ′ 𝒟) & lifts-subs ξ ψ ⁻¹
                       ⦙ subs-sub (lifts ξ) (lifts ψ) 𝒟

--------------------------------------------------------------------------------

assoc-subs : ∀ {Γ Ξ Ψ Φ} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (φ : Ψ ⊢⋆ Φ)
                         → subs (subs ξ ψ) φ ≡ subs ξ (subs ψ φ)
assoc-subs ξ ψ ∙       = refl
assoc-subs ξ ψ (φ , 𝒟) = _,_ & assoc-subs ξ ψ φ ⊗ subs-sub ξ ψ 𝒟

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

_∋⋆_ = _⊇_

-- putᵣ

getᵣ = ren∋

pattern wkᵣ = _⊇_.drop

pattern liftᵣ = _⊇_.keep

idᵣ = id⊇

ren′ = ren

wk′ = wk

_○_ = _∘⊇_

--------------------------------------------------------------------------------

-- natgetᵣ

idgetᵣ = id-ren∋

idren′ = id-ren

--------------------------------------------------------------------------------

-- postulate
--   nope : ∀ {X A} → {Γ Γ′ : List X}
--                  → Γ′ ⊇ Γ → Γ′ ∋ A
--                  → Γ′ ⊇ Γ , A

-- postulate
--   zap○ : ∀ {X A} → {Γ Γ′ Γ″ : List X}
--                  → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (𝒾 : Γ″ ∋ A)
--                  → drop η₁ ∘⊇ nope η₂ 𝒾 ≡ η₁ ∘⊇ η₂

lid○ = lid-∘⊇

rid○ = rid-∘⊇

--------------------------------------------------------------------------------

get○ = comp-ren∋

-- wk○

-- lift○

-- wklid○

-- wkrid○

-- liftwkrid○

ren○ = comp-ren

-- renlift○

-- renwk○

-- renliftwk○

--------------------------------------------------------------------------------

assoc○ = assoc-∘⊇

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

_⊢⋆′_ = _⊢⋆_

-- putₛ

getₛ = lookup

wkₛ = wks

liftₛ = lifts

idₛ = ids

sub′ = sub

cut′ = cut

_●_ : ∀ {Γ Ξ Ψ} → Ξ ⊢⋆ Ψ → Γ ⊢⋆ Ξ
                → Γ ⊢⋆ Ψ
ψ ● ξ = subs ξ ψ

--------------------------------------------------------------------------------

natgetₛ = wks-lookup

idgetₛ = ids-lookup

idsub′ = id-sub

--------------------------------------------------------------------------------

-- ⌊_⌋ = hyps

_◐_ : ∀ {Γ Ξ Ξ′} → Γ ⊢⋆ Ξ′ → Ξ′ ⊇ Ξ
                 → Γ ⊢⋆ Ξ
_◐_ = lookups

_◑_ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                 → Γ′ ⊢⋆ Ξ
_◑_ = rens

-- ⌊get⌋
-- ⌊wk⌋
-- ⌊lift⌋
-- ⌊id⌋
-- ⌊sub⌋
-- ⌊○⌋

--------------------------------------------------------------------------------

zap◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Γ ⊢ A true)
                    → lookups (ξ , 𝒟) (drop η) ≡ lookups ξ η
zap◐ ξ η 𝒟 = refl

rid◐ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
               → lookups ξ id⊇ ≡ ξ
rid◐ = id-lookups

--------------------------------------------------------------------------------

get◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒾 : Ξ ∋ A true)
                    → lookup (lookups ξ η) 𝒾 ≡ lookup ξ (ren∋ η 𝒾)
get◐ ξ η 𝒾 = lookups-lookup ξ η 𝒾 

wk◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                   → wks {A} (lookups ξ η) ≡ lookups (wks ξ) η
wk◐ ξ η = wks-lookups ξ η ⁻¹

lift◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ)
                     → lifts {A} (lookups ξ η) ≡ lookups (lifts ξ) (keep η)
lift◐ ξ η = lifts-lookups ξ η ⁻¹

postulate
  wkrid◐ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → lookups (wks {A} ξ) id⊇ ≡ wks ξ

postulate
  liftwkrid◐ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → lookups (lifts {A} ξ) (drop id⊇) ≡ wks ξ

sub◐ : ∀ {Γ Ξ Ξ′ A} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                    → sub (lookups ξ η) 𝒟 ≡ sub ξ (ren η 𝒟)
sub◐ ξ η 𝒟 = lookups-sub ξ η 𝒟 

sublift◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                          → sub (lifts {B} (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (keep η) 𝒟)
sublift◐ ξ η 𝒟 = lookups-lifts-sub ξ η 𝒟 

postulate
  subwk◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub (wks {B} (lookups ξ η)) 𝒟 ≡ sub (wks ξ) (ren η 𝒟)

postulate
  subliftwk◐ : ∀ {Γ Ξ Ξ′ A B} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (𝒟 : Ξ ⊢ A true)
                              → sub (wks {B} (lookups ξ η)) 𝒟 ≡ sub (lifts ξ) (ren (drop η) 𝒟)

--------------------------------------------------------------------------------

-- postulate
--   zap◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Γ′ ∋ A true)
--                       → rens (nope η 𝒾) (wks ξ) ≡ rens η ξ

lid◑ : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
               → rens id⊇ ξ ≡ ξ
lid◑ = id-rens

--------------------------------------------------------------------------------

zap● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Γ ⊢ A true)
                   → subs (ξ , 𝒟) (wks ψ) ≡ subs ξ ψ
zap● = absorb-subs

lid● : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
               → subs ids ξ ≡ ξ
lid● = lid-subs

rid● : ∀ {Γ Ξ} → (ξ : Γ ⊢⋆ Ξ)
               → subs ξ ids ≡ ξ
rid● = rid-subs

--------------------------------------------------------------------------------

get◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒾 : Ξ ∋ A true)
                    → lookup (rens η ξ) 𝒾 ≡ ren η (lookup ξ 𝒾)
get◑ η ξ 𝒾 = rens-lookup η ξ 𝒾 

wk◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                   → wks {A} (rens η ξ) ≡ rens (drop η) ξ
wk◑ η ξ = drop-wks-rens η ξ ⁻¹

lift◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                     → lifts {A} (rens η ξ) ≡ rens (keep η) (lifts ξ)
lift◑ η ξ = keep-lifts-rens η ξ ⁻¹

postulate
  wklid◑ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → rens (drop {A = A} id⊇) ξ ≡ wks ξ

postulate
  liftwklid◑ : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → rens (keep {A = A} id⊇) (wks ξ) ≡ wks ξ

sub◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                    → sub (rens η ξ) 𝒟 ≡ ren η (sub ξ 𝒟)
sub◑ η ξ 𝒟 = rens-sub η ξ 𝒟 

sublift◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ , B true ⊢ A true)
                          → sub (lifts {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (lifts ξ) 𝒟)
sublift◑ η ξ 𝒟 = rens-lifts-sub η ξ 𝒟 

postulate
  subwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                          → sub (wks {B} (rens η ξ)) 𝒟 ≡ ren (drop η) (sub ξ 𝒟)

postulate
  subliftwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (𝒟 : Ξ ⊢ A true)
                              → sub (wks {B} (rens η ξ)) 𝒟 ≡ ren (keep η) (sub (wks ξ) 𝒟)

--------------------------------------------------------------------------------

get● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒾 : Ψ ∋ A true)
                   → lookup (subs ξ ψ) 𝒾 ≡ sub ξ (lookup ψ 𝒾)
get● ξ ψ 𝒾 = subs-lookup ξ ψ 𝒾 

wk● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                  → wks {A} (subs ξ ψ) ≡ subs (wks ξ) ψ
wk● ξ ψ = wks-subs ξ ψ ⁻¹

lift● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                    → lifts {A} (subs ξ ψ) ≡ subs (lifts ξ) (lifts ψ)
lift● ξ ψ = lifts-subs ξ ψ ⁻¹

postulate
  wklid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → subs (wks {A} ids) ξ ≡ wks ξ

postulate
  wkrid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                     → subs (wks {A} ξ) ids ≡ wks ξ

postulate
  liftwkrid● : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → subs (lifts {A} ξ) (wks ids) ≡ wks ξ

sub● : ∀ {Γ Ξ Ψ A} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                   → sub (subs ξ ψ) 𝒟 ≡ sub ξ (sub ψ 𝒟)
sub● ξ ψ 𝒟 = subs-sub ξ ψ 𝒟 

sublift● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ , B true ⊢ A true)
                         → sub (lifts {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (lifts ψ) 𝒟)
sublift● ξ ψ 𝒟 = subs-lifts-sub ξ ψ 𝒟 

postulate
  subwk● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                         → sub (wks {B} (subs ξ ψ)) 𝒟 ≡ sub (wks ξ) (sub ψ 𝒟)

postulate
  subliftwk● : ∀ {Γ Ξ Ψ A B} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (𝒟 : Ψ ⊢ A true)
                             → sub (wks {B} (subs ξ ψ)) 𝒟 ≡ sub (lifts ξ) (sub (wks ψ) 𝒟)

--------------------------------------------------------------------------------

comp◐○ : ∀ {Γ Ξ Ξ′ Ξ″} → (ξ : Γ ⊢⋆ Ξ″) (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′)
                       → lookups ξ (η₁ ∘⊇ η₂) ≡ lookups (lookups ξ η₂) η₁
comp◐○ ξ η₁ η₂ = comp-lookups ξ η₁ η₂

comp◑○ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ′ ⊇ Γ) (η₂ : Γ″ ⊇ Γ′) (ξ : Γ ⊢⋆ Ξ)
                       → rens η₂ (rens η₁ ξ) ≡ rens (η₁ ∘⊇ η₂) ξ
comp◑○ η₁ η₂ ξ = comp-rens η₁ η₂ ξ ⁻¹

comp◑◐ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                       → rens η₁ (lookups ξ η₂) ≡ lookups (rens η₁ ξ) η₂
comp◑◐ η₁ ξ η₂ = rens-lookups η₁ ξ η₂ ⁻¹

comp◑● : ∀ {Γ Γ′ Ξ Ψ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                      → rens η (subs ξ ψ) ≡ subs (rens η ξ) ψ
comp◑● η ξ ψ = rens-subs η ξ ψ ⁻¹

comp●◐ : ∀ {Γ Ξ Ψ Ψ′} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ′) (η : Ψ′ ⊇ Ψ)
                      → subs ξ (lookups ψ η) ≡ lookups (subs ξ ψ) η
comp●◐ ξ ψ η = subs-lookups ξ ψ η ⁻¹

comp●◑ : ∀ {Γ Ξ Ξ′ Ψ} → (ξ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (ψ : Ξ ⊢⋆ Ψ)
                      → subs ξ (rens η ψ) ≡ subs (lookups ξ η) ψ
comp●◑ ξ η ψ = lookups-subs ξ η ψ ⁻¹

--------------------------------------------------------------------------------

assoc● : ∀ {Γ Ξ Ψ Φ} → (ξ : Γ ⊢⋆ Ξ) (ψ : Ξ ⊢⋆ Ψ) (φ : Ψ ⊢⋆ Φ)
                     → subs ξ (subs ψ φ) ≡ subs (subs ξ ψ) φ
assoc● ξ ψ φ = assoc-subs ξ ψ φ ⁻¹

