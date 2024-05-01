module A201802.LR0Lemmas where

open import A201802.Prelude
open import A201802.Category
open import A201802.Fin
open import A201802.FinLemmas
open import A201802.Vec
open import A201802.VecLemmas
open import A201802.LR0


--------------------------------------------------------------------------------
{-
                      GET (RENS e τ) I ≡ (REN e ∘ GET τ) I                      comp-REN-GET
                   GETS (RENS e₁ τ) e₂ ≡ (RENS e₁ ∘ GETS τ) e₂                  comp-RENS-GETS
             (GETS (LIFTS τ) ∘ keep) e ≡ (LIFTS ∘ GETS τ) e                     comp-LIFTS-GETS
                             GET IDS I ≡ VAR I                                  GET-VAR

                              REN id M ≡ M                                      id-REN
                             RENS id τ ≡ τ                                      id-RENS
                       REN (e₁ ∘ e₂) M ≡ (REN e₂ ∘ REN e₁) M                    comp-REN
                      RENS (e₁ ∘ e₂) τ ≡ (RENS e₂ ∘ RENS e₁) τ                  comp-RENS
                                                                                𝐑𝐄𝐍
                                                                                𝐑𝐄𝐍𝐒

                 (REN (keep e) ∘ WK) M ≡ (WK ∘ REN e) M                         comp-WK-REN-keep
               (RENS (keep e) ∘ WKS) τ ≡ (WKS ∘ RENS e) τ                       comp-WKS-RENS-keep
             (RENS (keep e) ∘ LIFTS) τ ≡ (LIFTS ∘ RENS e) τ                     comp-LIFTS-RENS

                      GET (SUBS τ υ) I ≡ (SUB τ ∘ GET υ) I                      comp-SUB-GET
                      SUB (GETS τ e) M ≡ (SUB τ ∘ REN e) M                      comp-SUB-REN
                  (SUB (τ , M) ∘ WK) N ≡ SUB τ N                                simp-SUB
                (SUBS (τ , M) ∘ WKS) υ ≡ SUBS τ υ                               simp-SUBS

                      SUB (RENS e τ) M ≡ (REN e ∘ SUB τ) M                      comp-REN-SUB
                     SUBS (RENS e τ) υ ≡ (RENS e ∘ SUBS τ) υ                    comp-RENS-SUBS
            (SUBS (LIFTS τ) ∘ LIFTS) υ ≡ (LIFTS ∘ SUBS τ) υ                     comp-LIFTS-SUBS

                             SUB IDS M ≡ M                                      id-SUB
                            SUBS IDS τ ≡ τ                                      lid-SUBS
                            SUBS τ IDS ≡ τ                                      rid-SUBS
                      SUB (SUBS τ υ) M ≡ (SUB τ ∘ SUB υ) M                      comp-SUB
                     SUBS (SUBS τ υ) ν ≡ (SUBS τ ∘ SUBS υ) ν                    assoc-SUBS
                                                                                𝐓𝐞𝐫𝐦𝐬
                                                                                𝐒𝐔𝐁

             (CUT M ∘ SUB (LIFTS τ)) N ≡ SUB (τ , M) N                          simp-CUT-SUB
-}
--------------------------------------------------------------------------------


comp-REN-GET : ∀ {g g′ n} → (e : g′ ≥ g) (τ : Terms g n) (I : Fin n)
                          → GET (RENS e τ) I ≡ (REN e ∘ GET τ) I
comp-REN-GET e (τ , M) zero    = refl
comp-REN-GET e (τ , N) (suc I) = comp-REN-GET e τ I


comp-RENS-GETS : ∀ {g g′ n n′} → (e₁ : g′ ≥ g) (τ : Terms g n′) (e₂ : n′ ≥ n)
                               → GETS (RENS e₁ τ) e₂ ≡ (RENS e₁ ∘ GETS τ) e₂
comp-RENS-GETS e₁ ∙       done      = refl
comp-RENS-GETS e₁ (τ , N) (drop e₂) = comp-RENS-GETS e₁ τ e₂
comp-RENS-GETS e₁ (τ , M) (keep e₂) = (_, REN e₁ M) & comp-RENS-GETS e₁ τ e₂


comp-LIFTS-GETS : ∀ {g n n′} → (τ : Terms g n′) (e : n′ ≥ n)
                             → (GETS (LIFTS τ) ∘ keep) e ≡ (LIFTS ∘ GETS τ) e
comp-LIFTS-GETS τ e = (_, VZ) & comp-RENS-GETS (drop id) τ e


GET-VAR : ∀ {g} → (I : Fin g)
                → GET IDS I ≡ VAR I
GET-VAR zero    = refl
GET-VAR (suc I) = comp-REN-GET (drop id) IDS I
                ⋮ WK & GET-VAR I
                ⋮ (\ i′ → VAR (suc i′)) & id-REN∋ I


--------------------------------------------------------------------------------


id-REN : ∀ {g} → (M : Term g)
               → REN id M ≡ M
id-REN (VAR I)      = VAR & id-REN∋ I
id-REN (LAM M)      = LAM & id-REN M
id-REN (APP M N)    = APP & id-REN M ⊗ id-REN N
id-REN (PAIR M N)   = PAIR & id-REN M ⊗ id-REN N
id-REN (FST M)      = FST & id-REN M
id-REN (SND M)      = SND & id-REN M
id-REN UNIT         = refl
id-REN (ABORT M)    = ABORT & id-REN M
id-REN (LEFT M)     = LEFT & id-REN M
id-REN (RIGHT M)    = RIGHT & id-REN M
id-REN (CASE M N O) = CASE & id-REN M ⊗ id-REN N ⊗ id-REN O
id-REN TRUE         = refl
id-REN FALSE        = refl
id-REN (IF M N O)   = IF & id-REN M ⊗ id-REN N ⊗ id-REN O


id-RENS : ∀ {g n} → (τ : Terms g n)
                  → RENS id τ ≡ τ
id-RENS ∙       = refl
id-RENS (τ , M) = _,_ & id-RENS τ ⊗ id-REN M


comp-REN : ∀ {g g′ g″} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (M : Term g)
                       → REN (e₁ ∘ e₂) M ≡ (REN e₂ ∘ REN e₁) M
comp-REN e₁ e₂ (VAR I)      = VAR & comp-REN∋ e₁ e₂ I
comp-REN e₁ e₂ (LAM M)      = LAM & comp-REN (keep e₁) (keep e₂) M
comp-REN e₁ e₂ (APP M N)    = APP & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N
comp-REN e₁ e₂ (PAIR M N)   = PAIR & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N
comp-REN e₁ e₂ (FST M)      = FST & comp-REN e₁ e₂ M
comp-REN e₁ e₂ (SND M)      = SND & comp-REN e₁ e₂ M
comp-REN e₁ e₂ UNIT         = refl
comp-REN e₁ e₂ (ABORT M)    = ABORT & comp-REN e₁ e₂ M
comp-REN e₁ e₂ (LEFT M)     = LEFT & comp-REN e₁ e₂ M
comp-REN e₁ e₂ (RIGHT M)    = RIGHT & comp-REN e₁ e₂ M
comp-REN e₁ e₂ (CASE M N O) = CASE & comp-REN e₁ e₂ M
                                   ⊗ comp-REN (keep e₁) (keep e₂) N
                                   ⊗ comp-REN (keep e₁) (keep e₂) O
comp-REN e₁ e₂ TRUE         = refl
comp-REN e₁ e₂ FALSE        = refl
comp-REN e₁ e₂ (IF M N O)   = IF & comp-REN e₁ e₂ M
                                 ⊗ comp-REN e₁ e₂ N
                                 ⊗ comp-REN e₁ e₂ O


comp-RENS : ∀ {g g′ g″ n} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (τ : Terms g n)
                          → RENS (e₁ ∘ e₂) τ ≡ (RENS e₂ ∘ RENS e₁) τ
comp-RENS e₁ e₂ ∙       = refl
comp-RENS e₁ e₂ (τ , M) = _,_ & comp-RENS e₁ e₂ τ ⊗ comp-REN e₁ e₂ M


𝐑𝐄𝐍 : Presheaf 𝐆𝐄𝐐 Term
𝐑𝐄𝐍 = record
        { ℱ     = REN
        ; idℱ   = funext! id-REN
        ; compℱ = \ e₁ e₂ → funext! (comp-REN e₁ e₂)
        }


𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf 𝐆𝐄𝐐 (\ g → Terms g n)
𝐑𝐄𝐍𝐒 = record
         { ℱ     = RENS
         ; idℱ   = funext! id-RENS
         ; compℱ = \ e₁ e₂ → funext! (comp-RENS e₁ e₂)
         }


--------------------------------------------------------------------------------


comp-WK-REN-keep : ∀ {g g′} → (e : g′ ≥ g) (M : Term g)
                            → (REN (keep e) ∘ WK) M ≡ (WK ∘ REN e) M
comp-WK-REN-keep e M = comp-REN (drop id) (keep e) M ⁻¹
                     ⋮ (\ e′ → REN (drop e′) M) & (lid∘ e ⋮ rid∘ e ⁻¹)
                     ⋮ comp-REN e (drop id) M


comp-WKS-RENS-keep : ∀ {g g′ n} → (e : g′ ≥ g) (τ : Terms g n)
                                → (RENS (keep e) ∘ WKS) τ ≡ (WKS ∘ RENS e) τ
comp-WKS-RENS-keep e ∙       = refl
comp-WKS-RENS-keep e (τ , M) = _,_ & comp-WKS-RENS-keep e τ ⊗ comp-WK-REN-keep e M


comp-LIFTS-RENS : ∀ {g g′ n} → (e : g′ ≥ g) (τ : Terms g n)
                             → (RENS (keep e) ∘ LIFTS) τ ≡ (LIFTS ∘ RENS e) τ
comp-LIFTS-RENS e τ = (_, VZ) & comp-WKS-RENS-keep e τ


--------------------------------------------------------------------------------


comp-SUB-GET : ∀ {g n m} → (τ : Terms g n) (υ : Terms n m) (I : Fin m)
                         → GET (SUBS τ υ) I ≡ (SUB τ ∘ GET υ) I
comp-SUB-GET τ (υ , M) zero    = refl
comp-SUB-GET τ (υ , N) (suc I) = comp-SUB-GET τ υ I


comp-SUB-REN : ∀ {g n n′} → (τ : Terms g n′) (e : n′ ≥ n) (M : Term n)
                          → SUB (GETS τ e) M ≡ (SUB τ ∘ REN e) M
comp-SUB-REN τ e (VAR I)      = comp-GET-REN∋ τ e I
comp-SUB-REN τ e (LAM M)      = LAM & ( (\ τ′ → SUB τ′ M) & comp-LIFTS-GETS τ e ⁻¹
                                      ⋮ comp-SUB-REN (LIFTS τ) (keep e) M
                                      )
comp-SUB-REN τ e (APP M N)    = APP & comp-SUB-REN τ e M ⊗ comp-SUB-REN τ e N
comp-SUB-REN τ e (PAIR M N)   = PAIR & comp-SUB-REN τ e M ⊗ comp-SUB-REN τ e N
comp-SUB-REN τ e (FST M)      = FST & comp-SUB-REN τ e M
comp-SUB-REN τ e (SND M)      = SND & comp-SUB-REN τ e M
comp-SUB-REN τ e UNIT         = refl
comp-SUB-REN τ e (ABORT M)    = ABORT & comp-SUB-REN τ e M
comp-SUB-REN τ e (LEFT M)     = LEFT & comp-SUB-REN τ e M
comp-SUB-REN τ e (RIGHT M)    = RIGHT & comp-SUB-REN τ e M
comp-SUB-REN τ e (CASE M N O) = CASE & comp-SUB-REN τ e M
                                     ⊗ ( (\ τ′ → SUB τ′ N) & comp-LIFTS-GETS τ e ⁻¹
                                       ⋮ comp-SUB-REN (LIFTS τ) (keep e) N
                                       )
                                     ⊗ ( (\ τ′ → SUB τ′ O) & comp-LIFTS-GETS τ e ⁻¹
                                       ⋮ comp-SUB-REN (LIFTS τ) (keep e) O
                                       )
comp-SUB-REN τ e TRUE         = refl
comp-SUB-REN τ e FALSE        = refl
comp-SUB-REN τ e (IF M N O)   = IF & comp-SUB-REN τ e M
                                   ⊗ comp-SUB-REN τ e N
                                   ⊗ comp-SUB-REN τ e O


simp-SUB : ∀ {g n} → (τ : Terms g n) (M : Term g) (N : Term n)
                   → (SUB (τ , M) ∘ WK) N ≡ SUB τ N
simp-SUB τ M N = comp-SUB-REN (τ , M) (drop id) N ⁻¹
               ⋮ (\ τ′ → SUB τ′ N) & id-GETS τ


simp-SUBS : ∀ {g n m} → (τ : Terms g n) (M : Term g) (υ : Terms n m)
                      → (SUBS (τ , M) ∘ WKS) υ ≡ SUBS τ υ
simp-SUBS τ M ∙       = refl
simp-SUBS τ M (υ , N) = _,_ & simp-SUBS τ M υ ⊗ simp-SUB τ M N


--------------------------------------------------------------------------------


comp-REN-SUB : ∀ {g g′ n} → (e : g′ ≥ g) (τ : Terms g n) (M : Term n)
                          → SUB (RENS e τ) M ≡ (REN e ∘ SUB τ) M
comp-REN-SUB e τ (VAR I)      = comp-REN-GET e τ I
comp-REN-SUB e τ (LAM M)      = LAM & ( (\ τ′ → SUB τ′ M) & comp-LIFTS-RENS e τ ⁻¹
                                      ⋮ comp-REN-SUB (keep e) (LIFTS τ) M
                                      )
comp-REN-SUB e τ (APP M N)    = APP & comp-REN-SUB e τ M ⊗ comp-REN-SUB e τ N
comp-REN-SUB e τ (PAIR M N)   = PAIR & comp-REN-SUB e τ M ⊗ comp-REN-SUB e τ N
comp-REN-SUB e τ (FST M)      = FST & comp-REN-SUB e τ M
comp-REN-SUB e τ (SND M)      = SND & comp-REN-SUB e τ M
comp-REN-SUB e τ UNIT         = refl
comp-REN-SUB e τ (ABORT M)    = ABORT & comp-REN-SUB e τ M
comp-REN-SUB e τ (LEFT M)     = LEFT & comp-REN-SUB e τ M
comp-REN-SUB e τ (RIGHT M)    = RIGHT & comp-REN-SUB e τ M
comp-REN-SUB e τ (CASE M N O) = CASE & comp-REN-SUB e τ M
                                     ⊗ ( (\ τ′ → SUB τ′ N) & comp-LIFTS-RENS e τ ⁻¹
                                       ⋮ comp-REN-SUB (keep e) (LIFTS τ) N
                                       )
                                     ⊗ ( (\ τ′ → SUB τ′ O) & comp-LIFTS-RENS e τ ⁻¹
                                       ⋮ comp-REN-SUB (keep e) (LIFTS τ) O
                                       )
comp-REN-SUB e τ TRUE         = refl
comp-REN-SUB e τ FALSE        = refl
comp-REN-SUB e τ (IF M N O)   = IF & comp-REN-SUB e τ M
                                   ⊗ comp-REN-SUB e τ N
                                   ⊗ comp-REN-SUB e τ O


comp-RENS-SUBS : ∀ {g g′ n m} → (e : g′ ≥ g) (τ : Terms g n) (υ : Terms n m)
                              → SUBS (RENS e τ) υ ≡ (RENS e ∘ SUBS τ) υ
comp-RENS-SUBS e τ ∙       = refl
comp-RENS-SUBS e τ (υ , M) = _,_ & comp-RENS-SUBS e τ υ ⊗ comp-REN-SUB e τ M


comp-LIFTS-SUBS : ∀ {g n m} → (τ : Terms g n) (υ : Terms n m)
                            → (SUBS (LIFTS τ) ∘ LIFTS) υ ≡ (LIFTS ∘ SUBS τ) υ
comp-LIFTS-SUBS τ υ = (_, VZ) & ( simp-SUBS (WKS τ) VZ υ
                                ⋮ comp-RENS-SUBS (drop id) τ υ
                                )


--------------------------------------------------------------------------------


id-SUB : ∀ {g} → (M : Term g)
               → SUB IDS M ≡ M
id-SUB (VAR I)      = GET-VAR I
id-SUB (LAM M)      = LAM & id-SUB M
id-SUB (APP M N)    = APP & id-SUB M ⊗ id-SUB N
id-SUB (PAIR M N)   = PAIR & id-SUB M ⊗ id-SUB N
id-SUB (FST M)      = FST & id-SUB M
id-SUB (SND M)      = SND & id-SUB M
id-SUB UNIT         = refl
id-SUB (ABORT M)    = ABORT & id-SUB M
id-SUB (LEFT M)     = LEFT & id-SUB M
id-SUB (RIGHT M)    = RIGHT & id-SUB M
id-SUB (CASE M N O) = CASE & id-SUB M ⊗ id-SUB N ⊗ id-SUB O
id-SUB TRUE         = refl
id-SUB FALSE        = refl
id-SUB (IF M N O)   = IF & id-SUB M ⊗ id-SUB N ⊗ id-SUB O


lid-SUBS : ∀ {g n} → (τ : Terms g n)
                   → SUBS IDS τ ≡ τ
lid-SUBS ∙       = refl
lid-SUBS (τ , M) = _,_ & lid-SUBS τ ⊗ id-SUB M


rid-SUBS : ∀ {g n} → (τ : Terms g n)
                   → SUBS τ IDS ≡ τ
rid-SUBS ∙       = refl
rid-SUBS (τ , M) = (_, M) & ( simp-SUBS τ M IDS
                            ⋮ rid-SUBS τ
                            )


comp-SUB : ∀ {g m n} → (τ : Terms g n) (υ : Terms n m) (M : Term m)
                     → SUB (SUBS τ υ) M ≡ (SUB τ ∘ SUB υ) M
comp-SUB τ υ (VAR I)      = comp-SUB-GET τ υ I
comp-SUB τ υ (LAM M)      = LAM & ( (\ τ′ → SUB τ′ M) & comp-LIFTS-SUBS τ υ ⁻¹
                                  ⋮ comp-SUB (LIFTS τ) (LIFTS υ) M
                                  )
comp-SUB τ υ (APP M N)    = APP & comp-SUB τ υ M ⊗ comp-SUB τ υ N
comp-SUB τ υ (PAIR M N)   = PAIR & comp-SUB τ υ M ⊗ comp-SUB τ υ N
comp-SUB τ υ (FST M)      = FST & comp-SUB τ υ M
comp-SUB τ υ (SND M)      = SND & comp-SUB τ υ M
comp-SUB τ υ UNIT         = refl
comp-SUB τ υ (ABORT M)    = ABORT & comp-SUB τ υ M
comp-SUB τ υ (LEFT M)     = LEFT & comp-SUB τ υ M
comp-SUB τ υ (RIGHT M)    = RIGHT & comp-SUB τ υ M
comp-SUB τ υ (CASE M N O) = CASE & comp-SUB τ υ M
                                 ⊗ ( (\ τ′ → SUB τ′ N) & comp-LIFTS-SUBS τ υ ⁻¹
                                   ⋮ comp-SUB (LIFTS τ) (LIFTS υ) N
                                   )
                                 ⊗ ( (\ τ′ → SUB τ′ O) & comp-LIFTS-SUBS τ υ ⁻¹
                                   ⋮ comp-SUB (LIFTS τ) (LIFTS υ) O
                                   )
comp-SUB τ υ TRUE         = refl
comp-SUB τ υ FALSE        = refl
comp-SUB τ υ (IF M N O)   = IF & comp-SUB τ υ M
                               ⊗ comp-SUB τ υ N
                               ⊗ comp-SUB τ υ O


assoc-SUBS : ∀ {g n m l} → (τ : Terms g n) (υ : Terms n m) (ν : Terms m l)
                         → SUBS (SUBS τ υ) ν ≡ (SUBS τ ∘ SUBS υ) ν
assoc-SUBS τ υ ∙       = refl
assoc-SUBS τ υ (ν , M) = _,_ & assoc-SUBS τ υ ν ⊗ comp-SUB τ υ M


instance
  𝐓𝐞𝐫𝐦𝐬 : Category Nat Terms
  𝐓𝐞𝐫𝐦𝐬 = record
            { id     = IDS
            ; _∘_    = flip SUBS
            ; lid∘   = rid-SUBS
            ; rid∘   = lid-SUBS
            ; assoc∘ = \ ν υ τ → assoc-SUBS τ υ ν ⁻¹
            }


𝐒𝐔𝐁 : Presheaf 𝐓𝐞𝐫𝐦𝐬 Term
𝐒𝐔𝐁 = record
        { ℱ     = SUB
        ; idℱ   = funext! id-SUB
        ; compℱ = \ υ τ → funext! (comp-SUB τ υ)
        }


--------------------------------------------------------------------------------


simp-CUT-SUB : ∀ {g n} → (M : Term g) (τ : Terms g n) (N : Term (suc n))
                       → (CUT M ∘ SUB (LIFTS τ)) N ≡ SUB (τ , M) N
simp-CUT-SUB M τ N = comp-SUB (IDS , M) (LIFTS τ) N ⁻¹
                   ⋮ (\ τ′ → SUB (τ′ , M) N) & ( simp-SUBS IDS M τ
                                                ⋮ lid-SUBS τ
                                                )


--------------------------------------------------------------------------------
