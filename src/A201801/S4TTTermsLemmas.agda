module A201801.S4TTTermsLemmas where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.S4TTTerms


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

                  (MREN e₁ ∘ REN e₂) M ≡ (REN e₂ ∘ MREN e₁) M                   comp-REN-MREN
                (MRENS e₁ ∘ RENS e₂) τ ≡ (RENS e₂ ∘ MRENS e₁) τ                 comp-RENS-MRENS
                   (MRENS e ∘ LIFTS) τ ≡ (LIFTS ∘ MRENS e) τ                    comp-LIFTS-MRENS
                           MRENS e IDS ≡ IDS                                    id-MRENS-IDS

                     GET (MRENS e τ) I ≡ (MREN e ∘ GET τ) I                     comp-MREN-GET
                    GET (MRENS* e τ) I ≡ (MREN e ∘ GET τ) I                     comp-MREN-GET*
                  GETS (MRENS e₁ τ) e₂ ≡ (MRENS e₁ ∘ GETS τ) e₂                 comp-MRENS-GETS
                 GETS (MRENS* e₁ τ) e₂ ≡ (MRENS* e₁ ∘ GETS τ) e₂                comp-MRENS*-GETS
           (GETS (MLIFTS* τ) ∘ keep) e ≡ (MLIFTS* ∘ GETS τ) e                   comp-MLIFTS*-GETS
                           GET MIDS* I ≡ MVAR I                                 GET-MVAR

                             MREN id M ≡ M                                      id-MREN
                            MRENS id τ ≡ τ                                      id-MRENS
                           MRENS* id τ ≡ τ                                      id-MRENS*
                      MREN (e₁ ∘ e₂) M ≡ (MREN e₂ ∘ MREN e₁) M                  comp-MREN
                     MRENS (e₁ ∘ e₂) τ ≡ (MRENS e₂ ∘ MRENS e₁) τ                comp-MRENS
                    MRENS* (e₁ ∘ e₂) τ ≡ (MRENS* e₂ ∘ MRENS* e₁) τ              comp-MRENS*
                                                                                𝐌𝐑𝐄𝐍
                                                                                𝐌𝐑𝐄𝐍𝐒
                                                                                𝐌𝐑𝐄𝐍𝐒*

               (MREN (keep e) ∘ MWK) M ≡ (MWK ∘ MREN e) M                       comp-MWK-MREN-keep
             (MRENS (keep e) ∘ MWKS) τ ≡ (MWKS ∘ MRENS e) τ                     comp-MWKS-MRENS-keep
           (MRENS* (keep e) ∘ MWKS*) τ ≡ (MWKS* ∘ MRENS* e) τ                   comp-MWKS*-MRENS*-keep
         (MRENS* (keep e) ∘ MLIFTS*) τ ≡ (MLIFTS* ∘ MRENS* e) τ                 comp-MLIFTS*-MRENS*

                      GET (SUBS τ υ) I ≡ (SUB τ ∘ GET υ) I                      comp-SUB-GET
                      SUB (GETS τ e) M ≡ (SUB τ ∘ REN e) M                      comp-SUB-REN
                  (SUB (τ , M) ∘ WK) N ≡ SUB τ N                                id-cons-WK-SUB
                (SUBS (τ , M) ∘ WKS) υ ≡ SUBS τ υ                               id-cons-WKS-SUBS

                      SUB (RENS e τ) M ≡ (REN e ∘ SUB τ) M                      comp-REN-SUB
                     SUBS (RENS e τ) υ ≡ (RENS e ∘ SUBS τ) υ                    comp-RENS-SUBS
            (SUBS (LIFTS τ) ∘ LIFTS) υ ≡ (LIFTS ∘ SUBS τ) υ                     comp-LIFTS-SUBS

          (SUB (MRENS e τ) ∘ MREN e) M ≡ (MREN e ∘ SUB τ) M                     comp-MREN-SUB
        (SUBS (MRENS e τ) ∘ MRENS e) υ ≡ (MRENS e ∘ SUBS τ) υ                   comp-MRENS-SUBS

                             SUB IDS M ≡ M                                      id-SUB
                            SUBS IDS τ ≡ τ                                      lid-SUBS
                            SUBS τ IDS ≡ τ                                      rid-SUBS
                      SUB (SUBS τ υ) M ≡ (SUB τ ∘ SUB υ) M                      comp-SUB
                     SUBS (SUBS τ υ) ν ≡ (SUBS τ ∘ SUBS υ) ν                    assoc-SUBS
                                                                                𝐒𝟒𝐓𝐞𝐫𝐦𝐬
                                                                                𝐒𝐔𝐁

                     GET (MSUBS τ υ) I ≡ (MSUB τ ∘ GET υ) I                     comp-MSUB-GET
                    GET (MSUBS* τ υ) I ≡ (MSUB τ ∘ GET υ) I                     comp-MSUB-GET*
                    (REN e ∘ MSUB τ) M ≡ (MSUB τ ∘ REN e) M                     comp-MSUB-REN
                  (RENS e ∘ MSUBS τ) υ ≡ (MSUBS τ ∘ RENS e) υ                   comp-MSUBS-RENS
                   (LIFTS ∘ MSUBS τ) υ ≡ (MSUBS τ ∘ LIFTS) υ                    comp-MSUBS-LIFTS
                     MSUB (GETS τ e) M ≡ (MSUB τ ∘ MREN e) M                    comp-MSUB-MREN
                (MSUB (τ , M) ∘ MWK) N ≡ MSUB τ N                               id-cons-MWK-MSUB
              (MSUBS (τ , M) ∘ MWKS) υ ≡ MSUBS τ υ                              id-cons-MWKS-MSUBS
            (MSUBS* (τ , M) ∘ MWKS*) υ ≡ MSUBS* τ υ                             id-cons-MWKS*-MSUBS*

                   MSUB (MRENS* e τ) M ≡ (MREN e ∘ MSUB τ) M                    comp-MREN-MSUB
                  MSUBS (MRENS* e τ) υ ≡ (MRENS e ∘ MSUBS τ) υ                  comp-MRENS-MSUBS
          (MSUBS (MLIFTS* τ) ∘ MWKS) υ ≡ (MWKS ∘ MSUBS τ) υ                     comp-MWKS-MSUBS
                 MSUBS* (MRENS* e τ) υ ≡ (MRENS* e ∘ MSUBS* τ) υ                comp-MRENS*-MSUBS*
        (MSUBS* (MLIFTS* τ) ∘ MWKS*) υ ≡ (MWKS* ∘ MSUBS* τ) υ                   comp-MWKS*-MSUBS*
      (MSUBS* (MLIFTS* τ) ∘ MLIFTS*) υ ≡ (MLIFTS* ∘ MSUBS* τ) υ                 comp-MLIFTS*-MSUBS*

          (SUB (MSUBS τ υ) ∘ MSUB τ) M ≡ (MSUB τ ∘ SUB υ) M                     comp-MSUB-SUB

                          MSUB MIDS* M ≡ M                                      id-MSUB
                         MSUBS MIDS* τ ≡ τ                                      id-MSUBS
                        MSUBS* MIDS* τ ≡ τ                                      lid-MSUBS*
                        MSUBS* τ MIDS* ≡ τ                                      rid-MSUBS*
                   MSUB (MSUBS* τ υ) M ≡ (MSUB τ ∘ MSUB υ) M                    comp-MSUB
                  MSUBS (MSUBS* τ υ) ν ≡ (MSUBS τ ∘ MSUBS υ) ν                  comp-MSUBS
                 MSUBS* (MSUBS* τ υ) ν ≡ (MSUBS* τ ∘ MSUBS* υ) ν                assoc-MSUBS*
                                                                                𝐒𝟒𝐓𝐞𝐫𝐦𝐬*
                                                                                𝐌𝐒𝐔𝐁
                                                                                𝐌𝐒𝐔𝐁𝐒
                                                                                𝐌𝐒𝐔𝐁𝐒*
-}
--------------------------------------------------------------------------------


comp-REN-GET : ∀ {d g g′ n} → (e : g′ ≥ g) (τ : Terms d g n) (I : Fin n)
                            → GET (RENS e τ) I ≡ (REN e ∘ GET τ) I
comp-REN-GET e (τ , M) zero    = refl
comp-REN-GET e (τ , N) (suc I) = comp-REN-GET e τ I


GET-VAR : ∀ {d g} → (I : Fin g)
                  → GET (IDS {d = d}) I ≡ VAR I
GET-VAR zero    = refl
GET-VAR (suc I) = comp-REN-GET (drop id) IDS I
                ⋮ WK & GET-VAR I
                ⋮ (\ i′ → VAR (suc i′)) & id-REN∋ I


comp-RENS-GETS : ∀ {d g g′ n n′} → (e₁ : g′ ≥ g) (τ : Terms d g n′) (e₂ : n′ ≥ n)
                                 → GETS (RENS e₁ τ) e₂ ≡ (RENS e₁ ∘ GETS τ) e₂
comp-RENS-GETS e₁ ∙       done      = refl
comp-RENS-GETS e₁ (τ , N) (drop e₂) = comp-RENS-GETS e₁ τ e₂
comp-RENS-GETS e₁ (τ , M) (keep e₂) = (_, REN e₁ M) & comp-RENS-GETS e₁ τ e₂


comp-LIFTS-GETS : ∀ {d g n n′} → (τ : Terms d g n′) (e : n′ ≥ n)
                               → (GETS (LIFTS τ) ∘ keep) e ≡ (LIFTS ∘ GETS τ) e
comp-LIFTS-GETS τ e = (_, VZ) & comp-RENS-GETS (drop id) τ e


--------------------------------------------------------------------------------


id-REN : ∀ {d g} → (M : Term d g)
                 → REN id M ≡ M
id-REN (VAR I)      = VAR & id-REN∋ I
id-REN (LAM M)      = LAM & id-REN M
id-REN (APP M N)    = APP & id-REN M ⊗ id-REN N
id-REN (MVAR I)     = refl
id-REN (BOX M)      = refl
id-REN (LETBOX M N) = LETBOX & id-REN M ⊗ id-REN N


id-RENS : ∀ {d g n} → (τ : Terms d g n)
                    → RENS id τ ≡ τ
id-RENS ∙       = refl
id-RENS (τ , M) = _,_ & id-RENS τ ⊗ id-REN M


comp-REN : ∀ {d g g′ g″} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (M : Term d g)
                         → REN (e₁ ∘ e₂) M ≡ (REN e₂ ∘ REN e₁) M
comp-REN e₁ e₂ (VAR I)      = VAR & comp-REN∋ e₁ e₂ I
comp-REN e₁ e₂ (LAM M)      = LAM & comp-REN (keep e₁) (keep e₂) M
comp-REN e₁ e₂ (APP M N)    = APP & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N
comp-REN e₁ e₂ (MVAR I)     = refl
comp-REN e₁ e₂ (BOX M)      = refl
comp-REN e₁ e₂ (LETBOX M N) = LETBOX & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N


comp-RENS : ∀ {d g g′ g″ n} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (τ : Terms d g n)
                            → RENS (e₁ ∘ e₂) τ ≡ (RENS e₂ ∘ RENS e₁) τ
comp-RENS e₁ e₂ ∙       = refl
comp-RENS e₁ e₂ (τ , M) = _,_ & comp-RENS e₁ e₂ τ ⊗ comp-REN e₁ e₂ M


𝐑𝐄𝐍 : Presheaf 𝐆𝐄𝐐 (\ g → Σ Nat (\ d → Term d g))
𝐑𝐄𝐍 = record
        { ℱ     = \ { e (d , M) → d , REN e M }
        ; idℱ   = funext! (\ { (d , M) → (d ,_) & id-REN M })
        ; compℱ = \ e₁ e₂ → funext! (\ { (d , M) → (d ,_) & comp-REN e₁ e₂ M })
        }


𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf 𝐆𝐄𝐐 (\ g → Σ Nat (\ d → Terms d g n))
𝐑𝐄𝐍𝐒 = record
         { ℱ     = \ { e (d , τ) → d , RENS e τ }
         ; idℱ   = funext! (\ { (d , τ) → (d ,_) & id-RENS τ })
         ; compℱ = \ e₁ e₂ → funext! (\ { (d , τ) → (d ,_) & comp-RENS e₁ e₂ τ })
         }


--------------------------------------------------------------------------------


comp-WK-REN-keep : ∀ {d g g′} → (e : g′ ≥ g) (M : Term d g)
                              → (REN (keep e) ∘ WK) M ≡ (WK ∘ REN e) M
comp-WK-REN-keep e M = comp-REN (drop id) (keep e) M ⁻¹
                     ⋮ (\ e′ → REN (drop e′) M) & (lid∘ e ⋮ rid∘ e ⁻¹)
                     ⋮ comp-REN e (drop id) M


comp-WKS-RENS-keep : ∀ {d g g′ n} → (e : g′ ≥ g) (τ : Terms d g n)
                                  → (RENS (keep e) ∘ WKS) τ ≡ (WKS ∘ RENS e) τ
comp-WKS-RENS-keep e ∙       = refl
comp-WKS-RENS-keep e (τ , M) = _,_ & comp-WKS-RENS-keep e τ ⊗ comp-WK-REN-keep e M


comp-LIFTS-RENS : ∀ {d g g′ n} → (e : g′ ≥ g) (τ : Terms d g n)
                               → (RENS (keep e) ∘ LIFTS) τ ≡ (LIFTS ∘ RENS e) τ
comp-LIFTS-RENS e τ = (_, VZ) & comp-WKS-RENS-keep e τ


--------------------------------------------------------------------------------


comp-REN-MREN : ∀ {d d′ g g′} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (M : Term d g)
                              → (MREN e₁ ∘ REN e₂) M ≡ (REN e₂ ∘ MREN e₁) M
comp-REN-MREN e₁ e₂ (VAR I)      = refl
comp-REN-MREN e₁ e₂ (LAM M)      = LAM & comp-REN-MREN e₁ (keep e₂) M
comp-REN-MREN e₁ e₂ (APP M N)    = APP & comp-REN-MREN e₁ e₂ M ⊗ comp-REN-MREN e₁ e₂ N
comp-REN-MREN e₁ e₂ (MVAR I)     = refl
comp-REN-MREN e₁ e₂ (BOX M)      = refl
comp-REN-MREN e₁ e₂ (LETBOX M N) = LETBOX & comp-REN-MREN e₁ e₂ M ⊗ comp-REN-MREN (keep e₁) e₂ N


comp-RENS-MRENS : ∀ {d d′ g g′ n} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (τ : Terms d g n)
                                  → (MRENS e₁ ∘ RENS e₂) τ ≡ (RENS e₂ ∘ MRENS e₁) τ
comp-RENS-MRENS e₁ e₂ ∙       = refl
comp-RENS-MRENS e₁ e₂ (τ , M) = _,_ & comp-RENS-MRENS e₁ e₂ τ ⊗ comp-REN-MREN e₁ e₂ M


comp-LIFTS-MRENS : ∀ {d d′ g n} → (e : d′ ≥ d) (τ : Terms d g n)
                                → (MRENS e ∘ LIFTS) τ ≡ (LIFTS ∘ MRENS e) τ
comp-LIFTS-MRENS e τ = (_, VZ) & comp-RENS-MRENS e (drop id) τ


id-MRENS-IDS : ∀ {d d′ g} → (e : d′ ≥ d)
                          → MRENS e (IDS {g = g}) ≡ IDS
id-MRENS-IDS {g = zero}  e = refl
id-MRENS-IDS {g = suc g} e = comp-LIFTS-MRENS e IDS
                           ⋮ LIFTS & id-MRENS-IDS e


--------------------------------------------------------------------------------


comp-MREN-GET : ∀ {d d′ g n} → (e : d′ ≥ d) (τ : Terms d g n) (I : Fin n)
                             → GET (MRENS e τ) I ≡ (MREN e ∘ GET τ) I
comp-MREN-GET e (τ , M) zero    = refl
comp-MREN-GET e (τ , N) (suc I) = comp-MREN-GET e τ I


comp-MREN-GET* : ∀ {d d′ n} → (e : d′ ≥ d) (τ : Terms* d n) (I : Fin n)
                            → GET (MRENS* e τ) I ≡ (MREN e ∘ GET τ) I
comp-MREN-GET* e (τ , M) zero    = refl
comp-MREN-GET* e (τ , N) (suc I) = comp-MREN-GET* e τ I


comp-MRENS-GETS : ∀ {d d′ g n n′} → (e₁ : d′ ≥ d) (τ : Terms d g n′) (e₂ : n′ ≥ n)
                                  → GETS (MRENS e₁ τ) e₂ ≡ (MRENS e₁ ∘ GETS τ) e₂
comp-MRENS-GETS e₁ ∙       done      = refl
comp-MRENS-GETS e₁ (τ , N) (drop e₂) = comp-MRENS-GETS e₁ τ e₂
comp-MRENS-GETS e₁ (τ , M) (keep e₂) = (_, MREN e₁ M) & comp-MRENS-GETS e₁ τ e₂


comp-MRENS*-GETS : ∀ {d d′ n n′} → (e₁ : d′ ≥ d) (τ : Terms* d n′) (e₂ : n′ ≥ n)
                                 → GETS (MRENS* e₁ τ) e₂ ≡ (MRENS* e₁ ∘ GETS τ) e₂
comp-MRENS*-GETS e₁ τ e₂ = comp-MRENS-GETS e₁ τ e₂


comp-MLIFTS*-GETS : ∀ {d n n′} → (τ : Terms* d n′) (e : n′ ≥ n)
                               → (GETS (MLIFTS* τ) ∘ keep) e ≡ (MLIFTS* ∘ GETS τ) e
comp-MLIFTS*-GETS τ e = (_, MVZ) & comp-MRENS*-GETS (drop id) τ e


GET-MVAR : ∀ {d} → (I : Fin d)
                 → GET MIDS* I ≡ MVAR I
GET-MVAR zero    = refl
GET-MVAR (suc I) = comp-MREN-GET* (drop id) MIDS* I
                 ⋮ MWK & GET-MVAR I
                 ⋮ (\ i′ → MVAR (suc i′)) & id-REN∋ I


--------------------------------------------------------------------------------


id-MREN : ∀ {d g} → (M : Term d g)
                  → MREN id M ≡ M
id-MREN (VAR I)      = refl
id-MREN (LAM M)      = LAM & id-MREN M
id-MREN (APP M N)    = APP & id-MREN M ⊗ id-MREN N
id-MREN (MVAR I)     = MVAR & id-REN∋ I
id-MREN (BOX M)      = BOX & id-MREN M
id-MREN (LETBOX M N) = LETBOX & id-MREN M ⊗ id-MREN N


id-MRENS : ∀ {d g n} → (τ : Terms d g n)
                     → MRENS id τ ≡ τ
id-MRENS ∙       = refl
id-MRENS (τ , M) = _,_ & id-MRENS τ ⊗ id-MREN M


id-MRENS* : ∀ {d n} → (τ : Terms* d n)
                    → MRENS* id τ ≡ τ
id-MRENS* τ = id-MRENS τ


comp-MREN : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (M : Term d g)
                          → MREN (e₁ ∘ e₂) M ≡ (MREN e₂ ∘ MREN e₁) M
comp-MREN e₁ e₂ (VAR I)      = refl
comp-MREN e₁ e₂ (LAM M)      = LAM & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (APP M N)    = APP & comp-MREN e₁ e₂ M ⊗ comp-MREN e₁ e₂ N
comp-MREN e₁ e₂ (MVAR I)     = MVAR & comp-REN∋ e₁ e₂ I
comp-MREN e₁ e₂ (BOX M)      = BOX & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (LETBOX M N) = LETBOX & comp-MREN e₁ e₂ M ⊗ comp-MREN (keep e₁) (keep e₂) N


comp-MRENS : ∀ {d d′ d″ g n} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (τ : Terms d g n)
                             → MRENS (e₁ ∘ e₂) τ ≡ (MRENS e₂ ∘ MRENS e₁) τ
comp-MRENS e₁ e₂ ∙       = refl
comp-MRENS e₁ e₂ (τ , M) = _,_ & comp-MRENS e₁ e₂ τ ⊗ comp-MREN e₁ e₂ M


comp-MRENS* : ∀ {d d′ d″ n} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (τ : Terms* d n)
                            → MRENS* (e₁ ∘ e₂) τ ≡ (MRENS* e₂ ∘ MRENS* e₁) τ
comp-MRENS* e₁ e₂ τ = comp-MRENS e₁ e₂ τ


𝐌𝐑𝐄𝐍 : Presheaf 𝐆𝐄𝐐 (\ d → Σ Nat (\ g → Term d g))
𝐌𝐑𝐄𝐍 = record
         { ℱ     = \ { e (g , M) → g , MREN e M }
         ; idℱ   = funext! (\ { (g , M) → (g ,_) & id-MREN M })
         ; compℱ = \ e₁ e₂ → funext! (\ { (g , M) → (g ,_) & comp-MREN e₁ e₂ M })
         }


𝐌𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf 𝐆𝐄𝐐 (\ d → Σ Nat (\ g → Terms d g n))
𝐌𝐑𝐄𝐍𝐒 = record
          { ℱ     = \ { e (g , τ) → g , MRENS e τ }
          ; idℱ   = funext! (\ { (g , τ) → (g ,_) & id-MRENS τ })
          ; compℱ = \ e₁ e₂ → funext! (\ { (g , τ) → (g ,_) & comp-MRENS e₁ e₂ τ })
          }


𝐌𝐑𝐄𝐍𝐒* : ∀ {n} → Presheaf 𝐆𝐄𝐐 (flip Terms* n)
𝐌𝐑𝐄𝐍𝐒* = record
           { ℱ     = MRENS*
           ; idℱ   = funext! id-MRENS*
           ; compℱ = \ e₁ e₂ → funext! (comp-MRENS* e₁ e₂)
           }


--------------------------------------------------------------------------------


comp-MWK-MREN-drop : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
                                → MREN (drop e) M ≡ (MWK ∘ MREN e) M
comp-MWK-MREN-drop e M = (\ e′ → MREN (drop e′) M) & rid∘ e ⁻¹
                       ⋮ comp-MREN e (drop id) M


comp-MWK-MREN-keep : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
                                → (MREN (keep e) ∘ MWK) M ≡ (MWK ∘ MREN e) M
comp-MWK-MREN-keep e M = comp-MREN (drop id) (keep e) M ⁻¹
                       ⋮ (\ e′ → MREN (drop e′) M) & (lid∘ e ⋮ rid∘ e ⁻¹)
                       ⋮ comp-MREN e (drop id) M


comp-MWKS-MRENS-keep : ∀ {d d′ g n} → (e : d′ ≥ d) (τ : Terms d g n)
                                    → (MRENS (keep e) ∘ MWKS) τ ≡ (MWKS ∘ MRENS e) τ
comp-MWKS-MRENS-keep e ∙       = refl
comp-MWKS-MRENS-keep e (τ , M) = _,_ & comp-MWKS-MRENS-keep e τ ⊗ comp-MWK-MREN-keep e M


comp-MWKS*-MRENS*-keep : ∀ {d d′ n} → (e : d′ ≥ d) (τ : Terms* d n)
                                    → (MRENS* (keep e) ∘ MWKS*) τ ≡ (MWKS* ∘ MRENS* e) τ
comp-MWKS*-MRENS*-keep e τ = comp-MWKS-MRENS-keep e τ


comp-MLIFTS*-MRENS* : ∀ {d d′ n} → (e : d′ ≥ d) (τ : Terms* d n)
                                 → (MRENS* (keep e) ∘ MLIFTS*) τ ≡ (MLIFTS* ∘ MRENS* e) τ
comp-MLIFTS*-MRENS* e τ = (_, MVZ) & comp-MWKS*-MRENS*-keep e τ


--------------------------------------------------------------------------------


comp-SUB-GET : ∀ {d g n m} → (τ : Terms d g n) (υ : Terms d n m) (I : Fin m)
                           → GET (SUBS τ υ) I ≡ (SUB τ ∘ GET υ) I
comp-SUB-GET τ (υ , M) zero    = refl
comp-SUB-GET τ (υ , N) (suc I) = comp-SUB-GET τ υ I


comp-SUB-REN : ∀ {d g n n′} → (τ : Terms d g n′) (e : n′ ≥ n) (M : Term d n)
                            → SUB (GETS τ e) M ≡ (SUB τ ∘ REN e) M
comp-SUB-REN τ e (VAR I)      = comp-GET-REN∋ τ e I
comp-SUB-REN τ e (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-GETS τ e ⁻¹
                                      ⋮ comp-SUB-REN (LIFTS τ) (keep e) M
                                      )
comp-SUB-REN τ e (APP M N)    = APP & comp-SUB-REN τ e M ⊗ comp-SUB-REN τ e N
comp-SUB-REN τ e (MVAR I)     = refl
comp-SUB-REN τ e (BOX M)      = refl
comp-SUB-REN τ e (LETBOX M N) = LETBOX & comp-SUB-REN τ e M
                                       ⊗ ( (\ x′ → SUB x′ N) & comp-MRENS-GETS (drop id) τ e ⁻¹
                                         ⋮ comp-SUB-REN (MWKS τ) e N
                                         )


id-cons-WK-SUB : ∀ {d g n} → (τ : Terms d g n) (M : Term d g) (N : Term d n)
                           → (SUB (τ , M) ∘ WK) N ≡ SUB τ N
id-cons-WK-SUB τ M N = comp-SUB-REN (τ , M) (drop id) N ⁻¹
                     ⋮ (\ x′ → SUB x′ N) & id-GETS τ


id-cons-WKS-SUBS : ∀ {d g n m} → (τ : Terms d g n) (M : Term d g) (υ : Terms d n m)
                               → (SUBS (τ , M) ∘ WKS) υ ≡ SUBS τ υ
id-cons-WKS-SUBS τ M ∙       = refl
id-cons-WKS-SUBS τ M (υ , N) = _,_ & id-cons-WKS-SUBS τ M υ ⊗ id-cons-WK-SUB τ M N


--------------------------------------------------------------------------------


comp-REN-SUB : ∀ {d g g′ n} → (e : g′ ≥ g) (τ : Terms d g n) (M : Term d n)
                            → SUB (RENS e τ) M ≡ (REN e ∘ SUB τ) M
comp-REN-SUB e τ (VAR I)      = comp-REN-GET e τ I
comp-REN-SUB e τ (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-RENS e τ ⁻¹
                                      ⋮ comp-REN-SUB (keep e) (LIFTS τ) M
                                      )
comp-REN-SUB e τ (APP M N)    = APP & comp-REN-SUB e τ M ⊗ comp-REN-SUB e τ N
comp-REN-SUB e τ (MVAR I)     = refl
comp-REN-SUB e τ (BOX M)      = refl
comp-REN-SUB e τ (LETBOX M N) = LETBOX & comp-REN-SUB e τ M
                                       ⊗ ( (\ x′ → SUB x′ N) & comp-RENS-MRENS (drop id) e τ
                                         ⋮ comp-REN-SUB e (MWKS τ) N
                                         )


comp-RENS-SUBS : ∀ {d g g′ n m} → (e : g′ ≥ g) (τ : Terms d g n) (υ : Terms d n m)
                                → SUBS (RENS e τ) υ ≡ (RENS e ∘ SUBS τ) υ
comp-RENS-SUBS e τ ∙       = refl
comp-RENS-SUBS e τ (υ , M) = _,_ & comp-RENS-SUBS e τ υ ⊗ comp-REN-SUB e τ M


comp-LIFTS-SUBS : ∀ {d g n m} → (τ : Terms d g n) (υ : Terms d n m)
                              → (SUBS (LIFTS τ) ∘ LIFTS) υ ≡ (LIFTS ∘ SUBS τ) υ
comp-LIFTS-SUBS τ υ = (_, VZ) & ( id-cons-WKS-SUBS (WKS τ) VZ υ
                                ⋮ comp-RENS-SUBS (drop id) τ υ
                                )


--------------------------------------------------------------------------------



comp-MREN-SUB : ∀ {d d′ g n} → (e : d′ ≥ d) (τ : Terms d g n) (M : Term d n)
                             → (SUB (MRENS e τ) ∘ MREN e) M ≡ (MREN e ∘ SUB τ) M
comp-MREN-SUB e τ (VAR I)      = comp-MREN-GET e τ I
comp-MREN-SUB e τ (LAM M)      = LAM & ( (\ x′ → SUB x′ (MREN e M)) & comp-LIFTS-MRENS e τ ⁻¹
                                       ⋮ comp-MREN-SUB e (LIFTS τ) M
                                       )
comp-MREN-SUB e τ (APP M N)    = APP & comp-MREN-SUB e τ M ⊗ comp-MREN-SUB e τ N
comp-MREN-SUB e τ (MVAR I)     = refl
comp-MREN-SUB e τ (BOX M)      = refl
comp-MREN-SUB e τ (LETBOX M N) = LETBOX & comp-MREN-SUB e τ M
                                        ⊗ ( (\ x′ → SUB x′ (MREN (keep e) N)) & comp-MWKS-MRENS-keep e τ ⁻¹
                                          ⋮ comp-MREN-SUB (keep e) (MWKS τ) N
                                          )


comp-MRENS-SUBS : ∀ {d d′ g n m} → (e : d′ ≥ d) (τ : Terms d g n) (υ : Terms d n m)
                                 → (SUBS (MRENS e τ) ∘ MRENS e) υ ≡ (MRENS e ∘ SUBS τ) υ
comp-MRENS-SUBS e τ ∙       = refl
comp-MRENS-SUBS e τ (υ , M) = _,_ & comp-MRENS-SUBS e τ υ ⊗ comp-MREN-SUB e τ M


--------------------------------------------------------------------------------


id-SUB : ∀ {d g} → (M : Term d g)
                 → SUB IDS M ≡ M
id-SUB (VAR I)      = GET-VAR I
id-SUB (LAM M)      = LAM & id-SUB M
id-SUB (APP M N)    = APP & id-SUB M ⊗ id-SUB N
id-SUB (MVAR I)     = refl
id-SUB (BOX M)      = refl
id-SUB (LETBOX M N) = LETBOX & id-SUB M ⊗ ( (\ τ′ → SUB τ′ N) & id-MRENS-IDS (drop id)
                                          ⋮ id-SUB N
                                          )


lid-SUBS : ∀ {d g n} → (τ : Terms d g n)
                     → SUBS IDS τ ≡ τ
lid-SUBS ∙       = refl
lid-SUBS (τ , M) = _,_ & lid-SUBS τ ⊗ id-SUB M


rid-SUBS : ∀ {d g n} → (τ : Terms d g n)
                     → SUBS τ IDS ≡ τ
rid-SUBS ∙       = refl
rid-SUBS (τ , M) = (_, M) & ( id-cons-WKS-SUBS τ M IDS
                            ⋮ rid-SUBS τ
                            )


comp-SUB : ∀ {d g m n} → (τ : Terms d g n) (υ : Terms d n m) (M : Term d m)
                       → SUB (SUBS τ υ) M ≡ (SUB τ ∘ SUB υ) M
comp-SUB τ υ (VAR I)      = comp-SUB-GET τ υ I
comp-SUB τ υ (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-SUBS τ υ ⁻¹
                                  ⋮ comp-SUB (LIFTS τ) (LIFTS υ) M
                                  )
comp-SUB τ υ (APP M N)    = APP & comp-SUB τ υ M ⊗ comp-SUB τ υ N
comp-SUB τ υ (MVAR I)     = refl
comp-SUB τ υ (BOX M)      = refl
comp-SUB τ υ (LETBOX M N) = LETBOX & comp-SUB τ υ M
                                   ⊗ ( (\ x′ → SUB x′ N) & comp-MRENS-SUBS (drop id) τ υ ⁻¹
                                     ⋮ comp-SUB (MWKS τ) (MWKS υ) N
                                     )


assoc-SUBS : ∀ {d g n m l} → (τ : Terms d g n) (υ : Terms d n m) (ν : Terms d m l)
                           → SUBS (SUBS τ υ) ν ≡ (SUBS τ ∘ SUBS υ) ν
assoc-SUBS τ υ ∙       = refl
assoc-SUBS τ υ (ν , M) = _,_ & assoc-SUBS τ υ ν ⊗ comp-SUB τ υ M


instance
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬 : ∀ {d} → Category Nat (Terms d)
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬 = record
              { id     = IDS
              ; _∘_    = flip SUBS
              ; lid∘   = rid-SUBS
              ; rid∘   = lid-SUBS
              ; assoc∘ = \ ν υ τ → assoc-SUBS τ υ ν ⁻¹
              }


𝐒𝐔𝐁 : ∀ {d} → Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬 (Term d)
𝐒𝐔𝐁 = record
        { ℱ     = SUB
        ; idℱ   = funext! id-SUB
        ; compℱ = \ υ τ → funext! (comp-SUB τ υ)
        }


--------------------------------------------------------------------------------


comp-MSUB-GET : ∀ {d g n m} → (τ : Terms* d n) (υ : Terms n g m) (I : Fin m)
                            → GET (MSUBS τ υ) I ≡ (MSUB τ ∘ GET υ) I
comp-MSUB-GET τ (υ , M) zero    = refl
comp-MSUB-GET τ (υ , N) (suc I) = comp-MSUB-GET τ υ I


comp-MSUB-GET* : ∀ {d n m} → (τ : Terms* d n) (υ : Terms* n m) (I : Fin m)
                           → GET (MSUBS* τ υ) I ≡ (MSUB τ ∘ GET υ) I
comp-MSUB-GET* τ (υ , M) zero    = refl
comp-MSUB-GET* τ (υ , N) (suc I) = comp-MSUB-GET* τ υ I


comp-MSUB-REN : ∀ {d g g′ n} → (τ : Terms* d n) (e : g′ ≥ g) (M : Term n g)
                             → (REN e ∘ MSUB τ) M ≡ (MSUB τ ∘ REN e) M
comp-MSUB-REN τ e (VAR I)      = refl
comp-MSUB-REN τ e (LAM M)      = LAM & comp-MSUB-REN τ (keep e) M
comp-MSUB-REN τ e (APP M N)    = APP & comp-MSUB-REN τ e M ⊗ comp-MSUB-REN τ e N
comp-MSUB-REN τ e (MVAR I)     = comp-REN-SUB e ∙ (GET τ I) ⁻¹
comp-MSUB-REN τ e (BOX M)      = refl
comp-MSUB-REN τ e (LETBOX M N) = LETBOX & comp-MSUB-REN τ e M ⊗ comp-MSUB-REN (MLIFTS* τ) e N


comp-MSUBS-RENS : ∀ {d g g′ n m} → (τ : Terms* d n) (e : g′ ≥ g) (υ : Terms n g m)
                                 → (RENS e ∘ MSUBS τ) υ ≡ (MSUBS τ ∘ RENS e) υ
comp-MSUBS-RENS τ e ∙       = refl
comp-MSUBS-RENS τ e (υ , M) = _,_ & comp-MSUBS-RENS τ e υ ⊗ comp-MSUB-REN τ e M


comp-MSUBS-LIFTS : ∀ {d g n m} → (τ : Terms* d n) (υ : Terms n g m)
                               → (LIFTS ∘ MSUBS τ) υ ≡ (MSUBS τ ∘ LIFTS) υ
comp-MSUBS-LIFTS τ υ = (_, VZ) & comp-MSUBS-RENS τ (drop id) υ


comp-MSUB-MREN : ∀ {d g n n′} → (τ : Terms* d n′) (e : n′ ≥ n) (M : Term n g)
                              → MSUB (GETS τ e) M ≡ (MSUB τ ∘ MREN e) M
comp-MSUB-MREN τ e (VAR I)      = refl
comp-MSUB-MREN τ e (LAM M)      = LAM & comp-MSUB-MREN τ e M
comp-MSUB-MREN τ e (APP M N)    = APP & comp-MSUB-MREN τ e M ⊗ comp-MSUB-MREN τ e N
comp-MSUB-MREN τ e (MVAR I)     = SUB ∙ & comp-GET-REN∋ τ e I
comp-MSUB-MREN τ e (BOX M)      = BOX & comp-MSUB-MREN τ e M
comp-MSUB-MREN τ e (LETBOX M N) = LETBOX & comp-MSUB-MREN τ e M
                                         ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS*-GETS τ e ⁻¹
                                           ⋮ comp-MSUB-MREN (MLIFTS* τ) (keep e) N
                                           )


id-cons-MWK-MSUB : ∀ {d g n} → (τ : Terms* d n) (M : Term d zero) (N : Term n g)
                             → (MSUB (τ , M) ∘ MWK) N ≡ MSUB τ N
id-cons-MWK-MSUB τ M N = comp-MSUB-MREN (τ , M) (drop id) N ⁻¹
                       ⋮ (\ x′ → MSUB x′ N) & id-GETS τ


id-cons-MWKS-MSUBS : ∀ {d g n m} → (τ : Terms* d n) (M : Term d zero) (υ : Terms n g m)
                                 → (MSUBS (τ , M) ∘ MWKS) υ ≡ MSUBS τ υ
id-cons-MWKS-MSUBS τ M ∙       = refl
id-cons-MWKS-MSUBS τ M (υ , N) = _,_ & id-cons-MWKS-MSUBS τ M υ ⊗ id-cons-MWK-MSUB τ M N


id-cons-MWKS*-MSUBS* : ∀ {d n m} → (τ : Terms* d n) (M : Term d zero) (υ : Terms* n m)
                                 → (MSUBS* (τ , M) ∘ MWKS*) υ ≡ MSUBS* τ υ
id-cons-MWKS*-MSUBS* τ M υ = id-cons-MWKS-MSUBS τ M υ


--------------------------------------------------------------------------------


comp-MREN-MSUB : ∀ {d d′ g n} → (e : d′ ≥ d) (τ : Terms* d n) (M : Term n g)
                              → MSUB (MRENS* e τ) M ≡ (MREN e ∘ MSUB τ) M
comp-MREN-MSUB e τ (VAR I)      = refl
comp-MREN-MSUB e τ (LAM M)      = LAM & comp-MREN-MSUB e τ M
comp-MREN-MSUB e τ (APP M N)    = APP & comp-MREN-MSUB e τ M ⊗ comp-MREN-MSUB e τ N
comp-MREN-MSUB e τ (MVAR I)     = SUB ∙ & comp-MREN-GET* e τ I
                                ⋮ comp-MREN-SUB e ∙ (GET τ I)
comp-MREN-MSUB e τ (BOX M)      = BOX & comp-MREN-MSUB e τ M
comp-MREN-MSUB e τ (LETBOX M N) = LETBOX & comp-MREN-MSUB e τ M
                                         ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS*-MRENS* e τ ⁻¹
                                           ⋮ comp-MREN-MSUB (keep e) (MLIFTS* τ) N
                                           )


comp-MRENS-MSUBS : ∀ {d d′ g n m} → (e : d′ ≥ d) (τ : Terms* d n) (υ : Terms n g m)
                                  → MSUBS (MRENS* e τ) υ ≡ (MRENS e ∘ MSUBS τ) υ
comp-MRENS-MSUBS e τ ∙       = refl
comp-MRENS-MSUBS e τ (υ , M) = _,_ & comp-MRENS-MSUBS e τ υ ⊗ comp-MREN-MSUB e τ M


comp-MWKS-MSUBS : ∀ {d g n m} → (τ : Terms* d n) (υ : Terms n g m)
                              → (MSUBS (MLIFTS* τ) ∘ MWKS) υ ≡ (MWKS ∘ MSUBS τ) υ
comp-MWKS-MSUBS τ υ = id-cons-MWKS-MSUBS (MWKS* τ) MVZ υ
                    ⋮ comp-MRENS-MSUBS (drop id) τ υ


comp-MRENS*-MSUBS* : ∀ {d d′ n m} → (e : d′ ≥ d) (τ : Terms* d n) (υ : Terms* n m)
                                  → MSUBS* (MRENS* e τ) υ ≡ (MRENS* e ∘ MSUBS* τ) υ
comp-MRENS*-MSUBS* e τ υ = comp-MRENS-MSUBS e τ υ


comp-MWKS*-MSUBS* : ∀ {d n m} → (τ : Terms* d n) (υ : Terms* n m)
                              → (MSUBS* (MLIFTS* τ) ∘ MWKS*) υ ≡ (MWKS* ∘ MSUBS* τ) υ
comp-MWKS*-MSUBS* τ υ = id-cons-MWKS*-MSUBS* (MWKS* τ) MVZ υ
                      ⋮ comp-MRENS*-MSUBS* (drop id) τ υ


comp-MLIFTS*-MSUBS* : ∀ {d n m} → (τ : Terms* d n) (υ : Terms* n m)
                                → (MSUBS* (MLIFTS* τ) ∘ MLIFTS*) υ ≡ (MLIFTS* ∘ MSUBS* τ) υ
comp-MLIFTS*-MSUBS* τ υ = (_, MVZ) & comp-MWKS*-MSUBS* τ υ


--------------------------------------------------------------------------------


comp-MSUB-SUB : ∀ {d g n m} → (τ : Terms* d n) (υ : Terms n g m) (M : Term n m)
                            → (SUB (MSUBS τ υ) ∘ MSUB τ) M ≡ (MSUB τ ∘ SUB υ) M
comp-MSUB-SUB τ υ (VAR I)      = comp-MSUB-GET τ υ I
comp-MSUB-SUB τ υ (LAM M)      = LAM & ( (\ x′ → SUB x′ (MSUB τ M)) & comp-MSUBS-LIFTS τ υ
                                       ⋮ comp-MSUB-SUB τ (LIFTS υ) M
                                       )
comp-MSUB-SUB τ υ (APP M N)    = APP & comp-MSUB-SUB τ υ M ⊗ comp-MSUB-SUB τ υ N
comp-MSUB-SUB τ υ (MVAR I)     = comp-SUB (MSUBS τ υ) ∙ (GET τ I) ⁻¹
comp-MSUB-SUB τ υ (BOX M)      = refl
comp-MSUB-SUB τ υ (LETBOX M N) = LETBOX & comp-MSUB-SUB τ υ M
                                        ⊗ ( (\ x′ → SUB x′ (MSUB (MWKS* τ , MVZ) N)) & comp-MWKS-MSUBS τ υ ⁻¹
                                          ⋮ comp-MSUB-SUB (MLIFTS* τ) (MWKS υ) N
                                          )


--------------------------------------------------------------------------------


id-MSUB : ∀ {d g} → (M : Term d g)
                  → MSUB MIDS* M ≡ M
id-MSUB (VAR I)      = refl
id-MSUB (LAM M)      = LAM & id-MSUB M
id-MSUB (APP M N)    = APP & id-MSUB M ⊗ id-MSUB N
id-MSUB (MVAR I)     = SUB ∙ & GET-MVAR I
id-MSUB (BOX M)      = BOX & id-MSUB M
id-MSUB (LETBOX M N) = LETBOX & id-MSUB M ⊗ id-MSUB N


id-MSUBS : ∀ {d g n} → (τ : Terms d g n)
                     → MSUBS MIDS* τ ≡ τ
id-MSUBS ∙       = refl
id-MSUBS (τ , M) = _,_ & id-MSUBS τ ⊗ id-MSUB M


lid-MSUBS* : ∀ {d n} → (τ : Terms* d n)
                     → MSUBS* MIDS* τ ≡ τ
lid-MSUBS* ∙       = refl
lid-MSUBS* (τ , M) = _,_ & lid-MSUBS* τ ⊗ id-MSUB M


rid-MSUBS* : ∀ {d n} → (τ : Terms* d n)
                     → MSUBS* τ MIDS* ≡ τ
rid-MSUBS* ∙       = refl
rid-MSUBS* (τ , M) = _,_ & ( id-cons-MWKS*-MSUBS* τ M MIDS*
                           ⋮ rid-MSUBS* τ
                           )
                         ⊗ id-SUB M


comp-MSUB : ∀ {d g n m} → (τ : Terms* d n) (υ : Terms* n m) (M : Term m g)
                        → MSUB (MSUBS* τ υ) M ≡ (MSUB τ ∘ MSUB υ) M
comp-MSUB τ υ (VAR I)      = refl
comp-MSUB τ υ (LAM M)      = LAM & comp-MSUB τ υ M
comp-MSUB τ υ (APP M N)    = APP & comp-MSUB τ υ M ⊗ comp-MSUB τ υ N
comp-MSUB τ υ (MVAR I)     = SUB ∙ & comp-MSUB-GET* τ υ I
                           ⋮ comp-MSUB-SUB τ ∙ (GET υ I)
comp-MSUB τ υ (BOX M)      = BOX & comp-MSUB τ υ M
comp-MSUB τ υ (LETBOX M N) = LETBOX & comp-MSUB τ υ M
                                    ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS*-MSUBS* τ υ ⁻¹
                                      ⋮ comp-MSUB (MLIFTS* τ) (MLIFTS* υ) N
                                      )


comp-MSUBS : ∀ {d g n m l} → (τ : Terms* d n) (υ : Terms* n m) (ν : Terms m g l)
                           → MSUBS (MSUBS* τ υ) ν ≡ (MSUBS τ ∘ MSUBS υ) ν
comp-MSUBS τ υ ∙       = refl
comp-MSUBS τ υ (ν , M) = _,_ & comp-MSUBS τ υ ν ⊗ comp-MSUB τ υ M


assoc-MSUBS* : ∀ {d n m l} → (τ : Terms* d n) (υ : Terms* n m) (ν : Terms* m l)
                           → MSUBS* (MSUBS* τ υ) ν ≡ (MSUBS* τ ∘ MSUBS* υ) ν
assoc-MSUBS* τ υ ∙       = refl
assoc-MSUBS* τ υ (ν , M) = _,_ & assoc-MSUBS* τ υ ν ⊗ comp-MSUB τ υ M


instance
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬* : Category Nat Terms*
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬* = record
               { id     = MIDS*
               ; _∘_    = flip MSUBS*
               ; lid∘   = rid-MSUBS*
               ; rid∘   = lid-MSUBS*
               ; assoc∘ = \ ν υ τ → assoc-MSUBS* τ υ ν ⁻¹
               }


𝐌𝐒𝐔𝐁 : Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬* (\ d → Term d zero)
𝐌𝐒𝐔𝐁 = record
         { ℱ     = MSUB
         ; idℱ   = funext! id-MSUB
         ; compℱ = \ υ τ → funext! (comp-MSUB τ υ)
         }


𝐌𝐒𝐔𝐁𝐒 : ∀ {g n} → Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬* (\ d → Terms d g n)
𝐌𝐒𝐔𝐁𝐒 = record
          { ℱ     = MSUBS
          ; idℱ   = funext! id-MSUBS
          ; compℱ = \ υ τ → funext! (comp-MSUBS τ υ)
          }


𝐌𝐒𝐔𝐁𝐒* : ∀ {n} → Presheaf 𝐒𝟒𝐓𝐞𝐫𝐦𝐬* (\ d → Terms* d n)
𝐌𝐒𝐔𝐁𝐒* = record
           { ℱ     = MSUBS*
           ; idℱ   = funext! lid-MSUBS*
           ; compℱ = \ υ τ → funext! (assoc-MSUBS* τ υ)
           }


--------------------------------------------------------------------------------
