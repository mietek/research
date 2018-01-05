module StdLPTTTermsLemmas where

open import Prelude
open import Fin
open import FinLemmas
open import Vec
open import StdLPTTTerms


--------------------------------------------------------------------------------


id-REN : ∀ {d g} → (M : Term d g)
                 → REN id≥ M ≡ M
id-REN (VAR i)      = VAR & id-renF i
id-REN (LAM M)      = LAM & id-REN M
id-REN (APP M N)    = APP & id-REN M ⊗ id-REN N
id-REN (MVAR i)     = refl
id-REN (BOX M)      = refl
id-REN (LETBOX M N) = LETBOX & id-REN M ⊗ id-REN N


comp-REN : ∀ {d g g′ g″} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (M : Term d g)
                         → REN (e₁ ∘≥ e₂) M ≡ REN e₂ (REN e₁ M)
comp-REN e₁ e₂ (VAR i)      = VAR & comp-renF e₁ e₂ i
comp-REN e₁ e₂ (LAM M)      = LAM & comp-REN (keep e₁) (keep e₂) M
comp-REN e₁ e₂ (APP M N)    = APP & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N
comp-REN e₁ e₂ (MVAR i)     = refl
comp-REN e₁ e₂ (BOX M)      = refl
comp-REN e₁ e₂ (LETBOX M N) = LETBOX & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N


--------------------------------------------------------------------------------


id-MREN : ∀ {d g} → (M : Term d g)
                  → MREN id≥ M ≡ M
id-MREN (VAR i)      = refl
id-MREN (LAM M)      = LAM & id-MREN M
id-MREN (APP M N)    = APP & id-MREN M ⊗ id-MREN N
id-MREN (MVAR i)     = MVAR & id-renF i
id-MREN (BOX M)      = BOX & id-MREN M
id-MREN (LETBOX M N) = LETBOX & id-MREN M ⊗ id-MREN N


comp-MREN : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (M : Term d g)
                          → MREN (e₁ ∘≥ e₂) M ≡ MREN e₂ (MREN e₁ M)
comp-MREN e₁ e₂ (VAR i)      = refl
comp-MREN e₁ e₂ (LAM M)      = LAM & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (APP M N)    = APP & comp-MREN e₁ e₂ M ⊗ comp-MREN e₁ e₂ N
comp-MREN e₁ e₂ (MVAR i)     = MVAR & comp-renF e₁ e₂ i
comp-MREN e₁ e₂ (BOX M)      = BOX & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (LETBOX M N) = LETBOX & comp-MREN e₁ e₂ M ⊗ comp-MREN (keep e₁) (keep e₂) N


comm-MREN-REN : ∀ {d d′ g g′} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (M : Term d g)
                              → MREN e₁ (REN e₂ M) ≡ REN e₂ (MREN e₁ M)
comm-MREN-REN e₁ e₂ (VAR i)      = refl
comm-MREN-REN e₁ e₂ (LAM M)      = LAM & comm-MREN-REN e₁ (keep e₂) M
comm-MREN-REN e₁ e₂ (APP M N)    = APP & comm-MREN-REN e₁ e₂ M ⊗ comm-MREN-REN e₁ e₂ N
comm-MREN-REN e₁ e₂ (MVAR i)     = refl
comm-MREN-REN e₁ e₂ (BOX M)      = refl
comm-MREN-REN e₁ e₂ (LETBOX M N) = LETBOX & comm-MREN-REN e₁ e₂ M ⊗ comm-MREN-REN (keep e₁) e₂ N


--------------------------------------------------------------------------------


comm-get-RENS : ∀ {d g g′ x} → (e : g′ ≥ g) (ζ : Terms d g x) (i : Fin x)
                             → get (RENS e ζ) i ≡ REN e (get ζ i)
comm-get-RENS e (ζ , M) zero    = refl
comm-get-RENS e (ζ , M) (suc i) = comm-get-RENS e ζ i


comm-get-WKS : ∀ {d g x} → (ζ : Terms d g x) (i : Fin x)
                         → get (WKS ζ) i ≡ WK (get ζ i)
comm-get-WKS ζ i = comm-get-RENS (drop id≥) ζ i


comm-get-IDS : ∀ {d g} → (i : Fin g)
                       → get (IDS {d}) i ≡ VAR i
comm-get-IDS zero    = refl
comm-get-IDS (suc i) = comm-get-WKS IDS i
                     ⋮ WK & comm-get-IDS i
                     ⋮ (\ i′ → VAR (suc i′)) & id-renF i


id-RENS : ∀ {d g x} → (ζ : Terms d g x)
                   → RENS id≥ ζ ≡ ζ
id-RENS ∙       = refl
id-RENS (ζ , M) = _,_ & id-RENS ζ ⊗ id-REN M


comp-RENS : ∀ {d g g′ g″ x} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (ζ : Terms d g x)
                            → RENS (e₁ ∘≥ e₂) ζ ≡ RENS e₂ (RENS e₁ ζ)
comp-RENS e₁ e₂ ∙       = refl
comp-RENS e₁ e₂ (ζ , M) = _,_ & comp-RENS e₁ e₂ ζ ⊗ comp-REN e₁ e₂ M


--------------------------------------------------------------------------------


comm-get-MRENS : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (i : Fin x)
                              → get (MRENS e ζ) i ≡ MREN e (get ζ i)
comm-get-MRENS e (ζ , M) zero    = refl
comm-get-MRENS e (ζ , M) (suc i) = comm-get-MRENS e ζ i


comm-get-MWKS : ∀ {d g x} → (ζ : Terms d g x) (i : Fin x)
                          → get (MWKS ζ) i ≡ MWK (get ζ i)
comm-get-MWKS ζ i = comm-get-MRENS (drop id≥) ζ i


id-MRENS : ∀ {d g x} → (ζ : Terms d g x)
                    → MRENS id≥ ζ ≡ ζ
id-MRENS ∙       = refl
id-MRENS (ζ , M) = _,_ & id-MRENS ζ ⊗ id-MREN M


comp-MRENS : ∀ {d d′ d″ g x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms d g x)
                             → MRENS (e₁ ∘≥ e₂) ζ ≡ MRENS e₂ (MRENS e₁ ζ)
comp-MRENS e₁ e₂ ∙       = refl
comp-MRENS e₁ e₂ (ζ , M) = _,_ & comp-MRENS e₁ e₂ ζ ⊗ comp-MREN e₁ e₂ M


comm-MRENS-RENS : ∀ {d d′ g g′ x} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (ζ : Terms d g x)
                                  → MRENS e₁ (RENS e₂ ζ) ≡ RENS e₂ (MRENS e₁ ζ)
comm-MRENS-RENS e₁ e₂ ∙       = refl
comm-MRENS-RENS e₁ e₂ (ζ , M) = _,_ & comm-MRENS-RENS e₁ e₂ ζ ⊗ comm-MREN-REN e₁ e₂ M


--------------------------------------------------------------------------------


-- xcomm-get-WKS : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (i : Fin x)
--                        → get (MRENS e (WKS ζ)) i ≡ MREN e (WK (get ζ i))
-- xcomm-get-WKS e (ζ , M) zero    = refl
-- xcomm-get-WKS e (ζ , N) (suc i) = xcomm-get-WKS e ζ i
--
--
-- xcomm-get-IDS : ∀ {d d′ g} → (e : d′ ≥ d) (i : Fin g)
--                      → get (MRENS e IDS) i ≡ VAR i
-- xcomm-get-IDS e zero    = refl
-- xcomm-get-IDS e (suc i) = xcomm-get-WKS e IDS i
--                   ⋮ comm-MREN-REN e (drop id≥) (get IDS i)
--                   ⋮ REN (drop id≥) & comm-get-MRENS e IDS i ⁻¹
--                   ⋮ WK & xcomm-get-IDS e i
--                   ⋮ VAR & (suc & id-renF i)


-- huh : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
--                  → MWK (MREN e M) ≡ MREN (keep e) (MWK M)
-- huh e (VAR i)      = refl
-- huh e (LAM M)      = LAM & huh e M
-- huh e (APP M N)    = APP & huh e M ⊗ huh e N
-- huh e (MVAR i)     = MVAR & ( suc & ( id-renF (renF e i)
--                                     ⋮ renF e & id-renF i ⁻¹
--                                     )
--                             )
-- huh e (BOX M)      = BOX & huh e M
-- huh e (LETBOX M N) = LETBOX & huh e M ⊗ ( comp-MREN (keep e) (keep (drop id≥)) N
--                                         ⋮ ( comp-MREN (keep (drop id≥)) (keep (keep e)) N
--                                           ⋮ (\ e′ → MREN (keep (drop e′)) N)
--                                             & (lid-∘≥ e ⋮ rid-∘≥ e ⁻¹)
--                                           ) ⁻¹
--                                         )
--
--
-- huhs : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x)
--                     → MWKS (MRENS e ζ) ≡ MRENS (keep e) (MWKS ζ)
-- huhs e ∙       = refl
-- huhs e (ζ , M) = _,_ & huhs e ζ ⊗ huh e M

-- wut : ∀ {d d′ g} → (e : d′ ≥ d)
--                  → MWKS (MRENS e (IDS {g = g})) ≡ MRENS (keep e) IDS
-- wut e = {!huhs e IDS!}

-- oops : ∀ {d d′ g x} → (e : d′ ≥ d) (ζ : Terms d g x) (M : Term d′ x)
--                     → SUB (MRENS e ζ) M ≡ {!!}
-- oops e ζ (VAR i)      = {!!}
-- oops e ζ (LAM M)      = {!!}
-- oops e ζ (APP M N)    = {!!}
-- oops e ζ (MVAR i)     = {!!}
-- oops e ζ (BOX M)      = {!!}
-- oops e ζ (LETBOX M N) = {!!}


-- xidSUB : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d′ g)
--                     → SUB (MRENS e IDS) M ≡ M
-- xidSUB e (VAR i)      = xcomm-get-IDS e i
-- xidSUB e (LAM M)      = LAM & ( (\ ζ → SUB ζ M)
--                                 & ( (_, VZ)
--                                     & comm-MRENS-RENS (drop id≥) e IDS
--                                   ) ⁻¹
--                               ⋮ xidSUB e M
--                               )
-- xidSUB e (APP M N)    = APP & xidSUB e M ⊗ xidSUB e N
-- xidSUB e (MVAR i)     = refl
-- xidSUB e (BOX M)      = refl
-- xidSUB e (LETBOX M N) = LETBOX & xidSUB e M ⊗ {!!}
-- -- xidSUB e (LETBOX M N) = LETBOX & xidSUB e M ⊗ ( (\ ζ → SUB ζ N)
-- --                                                 & huhs e IDS
-- --                                                 ⋮ {!(\ !}
-- --                                               ⋮ xidSUB (keep e) N
-- --                                               )


--------------------------------------------------------------------------------


postulate
  id-SUB : ∀ {d g} → (M : Term d g)
                   → SUB IDS M ≡ M
-- id-SUB (VAR i)      = comm-get-IDS i
-- id-SUB (LAM M)      = LAM & id-SUB M
-- id-SUB (APP M N)    = APP & id-SUB M ⊗ id-SUB N
-- id-SUB (MVAR i)     = refl
-- id-SUB (BOX M)      = refl
-- id-SUB (LETBOX M N) = LETBOX & id-SUB M ⊗ {!id-SUB N!}


--------------------------------------------------------------------------------


comm-get-MRENS₁ : ∀ {d d′ x} → (e : d′ ≥ d) (ζ : Terms₁ d x) (i : Fin x)
                             → get (MRENS₁ e ζ) i ≡ MREN e (get ζ i)
comm-get-MRENS₁ e ζ i = comm-get-MRENS e ζ i


comm-get-MWKS₁ : ∀ {d x} → (ζ : Terms₁ d x) (i : Fin x)
                         → get (MWKS ζ) i ≡ MWK (get ζ i)
comm-get-MWKS₁ ζ i = comm-get-MWKS ζ i


comm-get-MIDS₁ : ∀ {d} → (i : Fin d)
                       → get (MIDS₁ {d}) i ≡ MVAR i
comm-get-MIDS₁ zero    = refl
comm-get-MIDS₁ (suc i) = comm-get-MWKS₁ MIDS₁ i
                       ⋮ MWK & comm-get-MIDS₁ i
                       ⋮ (\ i′ → MVAR (suc i′)) & id-renF i


id-MRENS₁ : ∀ {d x} → (ζ : Terms₁ d x)
                   → MRENS₁ id≥ ζ ≡ ζ
id-MRENS₁ ζ = id-MRENS ζ


comp-MRENS₁ : ∀ {d d′ d″ x} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (ζ : Terms₁ d x)
                            → MRENS₁ (e₁ ∘≥ e₂) ζ ≡ MRENS₁ e₂ (MRENS₁ e₁ ζ)
comp-MRENS₁ e₁ e₂ ζ = comp-MRENS e₁ e₂ ζ


--------------------------------------------------------------------------------


postulate
  id-MSUB : ∀ {d g} → (M : Term d g)
                    → MSUB MIDS₁ M ≡ M
-- id-MSUB (VAR i)      = refl
-- id-MSUB (LAM M)      = LAM & id-MSUB M
-- id-MSUB (APP M N)    = APP & id-MSUB M ⊗ id-MSUB N
-- id-MSUB (MVAR i)     = {!!}
-- id-MSUB (BOX M)      = BOX & id-MSUB M
-- id-MSUB (LETBOX M N) = LETBOX & id-MSUB M ⊗ id-MSUB N


--------------------------------------------------------------------------------
