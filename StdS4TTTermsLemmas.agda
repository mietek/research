module StdS4TTTermsLemmas where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import StdS4TTTerms


--------------------------------------------------------------------------------
{-
                             REN id≥ M ≡ M                                      id-REN   ⎱ 𝐑𝐄𝐍
                       REN (e₁ ∘ e₂) M ≡ REN e₂ (REN e₁ M)                      comp-REN ⎰
                 (REN (keep e) ∘ WK) M ≡ (WK ∘ REN e) M                         comp-WK-REN-keep

                            MREN id≥ M ≡ M                                      id-MREN   ⎱ 𝐌𝐑𝐄𝐍
                      MREN (e₁ ∘ e₂) M ≡ MREN e₂ (MREN e₁ M)                    comp-MREN ⎰
                       MREN (drop e) M ≡ (MWK ∘ MREN e) M                       comp-MWK-MREN-drop
               (MREN (keep e) ∘ MWK) M ≡ (MWK ∘ MREN e) M                       comp-MWK-MREN-keep

                  (MREN e₁ ∘ REN e₂) M ≡ (REN e₂ ∘ MREN e₁) M                   comp-REN-MREN
                (MRENS e₁ ∘ RENS e₂) x ≡ (RENS e₂ ∘ MRENS e₁) x                 comp-RENS-MRENS
                   (MRENS e ∘ LIFTS) x ≡ (LIFTS ∘ MRENS e) x                    comp-LIFTS-MRENS

                            RENS id≥ x ≡ x                                      id-RENS   ⎱ 𝐑𝐄𝐍𝐒
                      RENS (e₁ ∘ e₂) x ≡ (RENS e₂ ∘ RENS e₁) x                  comp-RENS ⎰
               (RENS (keep e) ∘ WKS) x ≡ (WKS ∘ RENS e) x                       comp-WKS-RENS-keep
             (RENS (keep e) ∘ LIFTS) x ≡ (LIFTS ∘ RENS e) x                     comp-LIFTS-RENS

                           MRENS id≥ x ≡ x                                      id-MRENS   ⎱ 𝐌𝐑𝐄𝐍𝐒
                     MRENS (e₁ ∘ e₂) x ≡ (MRENS e₂ ∘ MRENS e₁) x                comp-MRENS ⎰
                      MRENS (drop e) x ≡ (MWKS ∘ MRENS e) x                     comp-MWKS-MRENS-drop
             (MRENS (keep e) ∘ MWKS) x ≡ (MWKS ∘ MRENS e) x                     comp-MWKS-MRENS-keep

                          MRENS₁ id≥ x ≡ x                                      id-MRENS₁   ⎱ 𝐌𝐑𝐄𝐍𝐒₁
                    MRENS₁ (e₁ ∘ e₂) x ≡ (MRENS₁ e₂ ∘ MRENS₁ e₁) x              comp-MRENS₁ ⎰
           (MRENS₁ (keep e) ∘ MWKS₁) x ≡ (MWKS₁ ∘ MRENS₁ e) x                   comp-MWKS₁-MRENS₁-keep
         (MRENS₁ (keep e) ∘ MLIFTS₁) x ≡ (MLIFTS₁ ∘ MRENS₁ e) x                 comp-MLIFTS₁-MRENS₁

                      GET (RENS e x) i ≡ (REN e ∘ GET x) i                      comp-REN-GET
                   GET (IDS {d = d}) i ≡ VAR i                                  VAR-id-GET

                     GET (MRENS e x) i ≡ (MREN e ∘ GET x) i                     comp-MREN-GET

                    GET (MRENS₁ e x) i ≡ (MREN e ∘ GET x) i                     comp-MREN-GET₁
                           GET MIDS₁ i ≡ MVAR i                                 MVAR-id-GET₁

                   GETS (RENS e₁ x) e₂ ≡ (RENS e₁ ∘ GETS x) e₂                  comp-RENS-GETS
               GETS (LIFTS x) (keep e) ≡ (LIFTS ∘ GETS x) e                     comp-LIFTS-GETS

                  GETS (MRENS e₁ x) e₂ ≡ (MRENS e₁ ∘ GETS x) e₂                 comp-MRENS-GETS

                 GETS (MRENS₁ e₁ x) e₂ ≡ (MRENS₁ e₁ ∘ GETS x) e₂                comp-MRENS₁-GETS
             GETS (MLIFTS₁ x) (keep e) ≡ (MLIFTS₁ ∘ GETS x) e                   comp-MLIFTS₁-GETS

                      GET (SUBS x y) i ≡ (SUB x ∘ GET y) i                      comp-SUB-GET

                     GET (MSUBS x y) i ≡ (MSUB x ∘ GET y) i                     comp-MSUB-GET

                    GET (MSUBS₁ x y) i ≡ (MSUB x ∘ GET y) i                     comp-MSUB-GET₁

                      SUB (GETS x e) M ≡ (SUB x ∘ REN e) M                      comp-SUB-REN

                    SUB (x , M) (WK N) ≡ SUB x N                                expand-SUB
                  SUBS (x , M) (WKS y) ≡ SUBS x y                               expand-SUBS

                      SUB (RENS e x) M ≡ (REN e ∘ SUB x) M                      comp-REN-SUB
                     SUBS (RENS e x) y ≡ (RENS e ∘ SUBS x) y                    comp-RENS-SUBS
              SUBS (LIFTS x) (LIFTS y) ≡ (LIFTS ∘ SUBS x) y                     comp-LIFTS-SUBS

                   SUB (MRENS e IDS) M ≡ M                                      id-MREN-SUB
            SUB (MRENS e x) (MREN e M) ≡ (MREN e ∘ SUB x) M                     comp-MREN-SUB
          SUBS (MRENS e x) (MRENS e y) ≡ (MRENS e ∘ SUBS x) y                   comp-MRENS-SUBS

                             SUB IDS M ≡ M                                      id-SUB   ⎱ 𝐒𝐔𝐁
                      SUB (SUBS x y) M ≡ (SUB x ∘ SUB y) M                      comp-SUB ⎰
                            SUBS IDS x ≡ x                                      lid-SUBS   ⎫
                            SUBS x IDS ≡ x                                      rid-SUBS   ⎬ 𝐒𝟒𝐓𝐞𝐫𝐦𝐬
                     SUBS (SUBS x y) z ≡ SUBS x (SUBS y z)                      assoc-SUBS ⎭

                    (REN e ∘ MSUB x) M ≡ (MSUB x ∘ REN e) M                     comp-MSUB-REN
                  (RENS e ∘ MSUBS x) y ≡ (MSUBS x ∘ RENS e) y                   comp-MSUBS-RENS
                   (LIFTS ∘ MSUBS x) y ≡ (MSUBS x ∘ LIFTS) y                    comp-MSUBS-LIFTS

                     MSUB (GETS x e) M ≡ (MSUB x ∘ MREN e) M                    comp-MSUB-MREN

                  MSUB (x , M) (MWK N) ≡ MSUB x N                               expand-MSUB
                MSUBS (x , M) (MWKS y) ≡ MSUBS x y                              expand-MSUBS
              MSUBS₁ (x , M) (MWKS₁ y) ≡ MSUBS₁ x y                             expand-MSUBS₁

                   MSUB (MRENS₁ e x) M ≡ (MREN e ∘ MSUB x) M                    comp-MREN-MSUB
                  MSUBS (MRENS₁ e x) y ≡ (MRENS e ∘ MSUBS x) y                  comp-MRENS-MSUBS
          (MSUBS (MLIFTS₁ x) ∘ MWKS) y ≡ (MWKS ∘ MSUBS x) y                     comp-MWKS-MSUBS
                 MSUBS₁ (MRENS₁ e x) y ≡ (MRENS₁ e ∘ MSUBS₁ x) y                comp-MRENS₁-MSUBS₁
        (MSUBS₁ (MLIFTS₁ x) ∘ MWKS₁) y ≡ (MWKS₁ ∘ MSUBS₁ x) y                   comp-MWKS₁-MSUBS₁
      (MSUBS₁ (MLIFTS₁ x) ∘ MLIFTS₁) y ≡ (MLIFTS₁ ∘ MSUBS₁ x) y                 comp-MLIFTS₁-MSUBS₁

          (SUB (MSUBS x y) ∘ MSUB x) M ≡ (MSUB x ∘ SUB y) M                     comp-MSUB-SUB

                          MSUB MIDS₁ M ≡ M                                      id-MSUB   ⎱ 𝐌𝐒𝐔𝐁
                   MSUB (MSUBS₁ x y) M ≡ (MSUB x ∘ MSUB y) M                    comp-MSUB ⎰
                        MSUBS₁ MIDS₁ x ≡ x                                      lid-MSUBS₁   ⎫
                        MSUBS₁ x MIDS₁ ≡ x                                      rid-MSUBS₁   ⎬ 𝐒𝟒𝐓𝐞𝐫𝐦𝐬₁
                 MSUBS₁ (MSUBS₁ x y) z ≡ MSUBS₁ x (MSUBS₁ y z)                  assoc-MSUBS₁ ⎭
-}
--------------------------------------------------------------------------------


id-REN : ∀ {d g} → (M : Term d g)
                 → REN id≥ M ≡ M
id-REN (VAR i)      = VAR & id-REN∋ i
id-REN (LAM M)      = LAM & id-REN M
id-REN (APP M N)    = APP & id-REN M ⊗ id-REN N
id-REN (MVAR i)     = refl
id-REN (BOX M)      = refl
id-REN (LETBOX M N) = LETBOX & id-REN M ⊗ id-REN N


comp-REN : ∀ {d g g′ g″} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (M : Term d g)
                         → REN (e₁ ∘ e₂) M ≡ REN e₂ (REN e₁ M)
comp-REN e₁ e₂ (VAR i)      = VAR & comp-REN∋ e₁ e₂ i
comp-REN e₁ e₂ (LAM M)      = LAM & comp-REN (keep e₁) (keep e₂) M
comp-REN e₁ e₂ (APP M N)    = APP & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N
comp-REN e₁ e₂ (MVAR i)     = refl
comp-REN e₁ e₂ (BOX M)      = refl
comp-REN e₁ e₂ (LETBOX M N) = LETBOX & comp-REN e₁ e₂ M ⊗ comp-REN e₁ e₂ N


𝐑𝐄𝐍 : Presheaf (\ g → Σ Nat (\ d → Term d g))
               (\ { e (d , M) → d , REN e M })
𝐑𝐄𝐍 = record
        { idℱ   = funext! (\ { (d , M) → (d ,_) & id-REN M })
        ; compℱ = \ e₁ e₂ → funext! (\ { (d , M) → (d ,_) & comp-REN e₁ e₂ M })
        }


comp-WK-REN-keep : ∀ {d g g′} → (e : g′ ≥ g) (M : Term d g)
                              → (REN (keep e) ∘ WK) M ≡ (WK ∘ REN e) M
comp-WK-REN-keep e M = comp-REN (drop id≥) (keep e) M ⁻¹
                     ⋮ (\ e′ → REN (drop e′) M) & (lid∘ e ⋮ rid∘ e ⁻¹)
                     ⋮ comp-REN e (drop id≥) M


--------------------------------------------------------------------------------


id-MREN : ∀ {d g} → (M : Term d g)
                  → MREN id≥ M ≡ M
id-MREN (VAR i)      = refl
id-MREN (LAM M)      = LAM & id-MREN M
id-MREN (APP M N)    = APP & id-MREN M ⊗ id-MREN N
id-MREN (MVAR i)     = MVAR & id-REN∋ i
id-MREN (BOX M)      = BOX & id-MREN M
id-MREN (LETBOX M N) = LETBOX & id-MREN M ⊗ id-MREN N


comp-MREN : ∀ {d d′ d″ g} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (M : Term d g)
                          → MREN (e₁ ∘ e₂) M ≡ MREN e₂ (MREN e₁ M)
comp-MREN e₁ e₂ (VAR i)      = refl
comp-MREN e₁ e₂ (LAM M)      = LAM & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (APP M N)    = APP & comp-MREN e₁ e₂ M ⊗ comp-MREN e₁ e₂ N
comp-MREN e₁ e₂ (MVAR i)     = MVAR & comp-REN∋ e₁ e₂ i
comp-MREN e₁ e₂ (BOX M)      = BOX & comp-MREN e₁ e₂ M
comp-MREN e₁ e₂ (LETBOX M N) = LETBOX & comp-MREN e₁ e₂ M ⊗ comp-MREN (keep e₁) (keep e₂) N


𝐌𝐑𝐄𝐍 : Presheaf (\ d → Σ Nat (\ g → Term d g))
                (\ { e (g , M) → g , MREN e M })
𝐌𝐑𝐄𝐍 = record
         { idℱ   = funext! (\ { (g , M) → (g ,_) & id-MREN M })
         ; compℱ = \ e₁ e₂ → funext! (\ { (g , M) → (g ,_) & comp-MREN e₁ e₂ M })
         }


comp-MWK-MREN-drop : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
                                → MREN (drop e) M ≡ (MWK ∘ MREN e) M
comp-MWK-MREN-drop e M = (\ e′ → MREN (drop e′) M) & rid∘ e ⁻¹
                       ⋮ comp-MREN e (drop id≥) M


comp-MWK-MREN-keep : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d g)
                                → (MREN (keep e) ∘ MWK) M ≡ (MWK ∘ MREN e) M
comp-MWK-MREN-keep e M = comp-MREN (drop id≥) (keep e) M ⁻¹
                       ⋮ (\ e′ → MREN (drop e′) M) & (lid∘ e ⋮ rid∘ e ⁻¹)
                       ⋮ comp-MREN e (drop id≥) M


--------------------------------------------------------------------------------


comp-REN-MREN : ∀ {d d′ g g′} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (M : Term d g)
                              → (MREN e₁ ∘ REN e₂) M ≡ (REN e₂ ∘ MREN e₁) M
comp-REN-MREN e₁ e₂ (VAR i)      = refl
comp-REN-MREN e₁ e₂ (LAM M)      = LAM & comp-REN-MREN e₁ (keep e₂) M
comp-REN-MREN e₁ e₂ (APP M N)    = APP & comp-REN-MREN e₁ e₂ M ⊗ comp-REN-MREN e₁ e₂ N
comp-REN-MREN e₁ e₂ (MVAR i)     = refl
comp-REN-MREN e₁ e₂ (BOX M)      = refl
comp-REN-MREN e₁ e₂ (LETBOX M N) = LETBOX & comp-REN-MREN e₁ e₂ M ⊗ comp-REN-MREN (keep e₁) e₂ N


comp-RENS-MRENS : ∀ {d d′ g g′ n} → (e₁ : d′ ≥ d) (e₂ : g′ ≥ g) (x : Terms d g n)
                                  → (MRENS e₁ ∘ RENS e₂) x ≡ (RENS e₂ ∘ MRENS e₁) x
comp-RENS-MRENS e₁ e₂ ∙       = refl
comp-RENS-MRENS e₁ e₂ (x , M) = _,_ & comp-RENS-MRENS e₁ e₂ x ⊗ comp-REN-MREN e₁ e₂ M


comp-LIFTS-MRENS : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms d g n)
                                → (MRENS e ∘ LIFTS) x ≡ (LIFTS ∘ MRENS e) x
comp-LIFTS-MRENS e x = (_, VZ) & comp-RENS-MRENS e (drop id≥) x


--------------------------------------------------------------------------------


id-RENS : ∀ {d g n} → (x : Terms d g n)
                    → RENS id≥ x ≡ x
id-RENS ∙       = refl
id-RENS (x , M) = _,_ & id-RENS x ⊗ id-REN M


comp-RENS : ∀ {d g g′ g″ n} → (e₁ : g′ ≥ g) (e₂ : g″ ≥ g′) (x : Terms d g n)
                            → RENS (e₁ ∘ e₂) x ≡ (RENS e₂ ∘ RENS e₁) x
comp-RENS e₁ e₂ ∙       = refl
comp-RENS e₁ e₂ (x , M) = _,_ & comp-RENS e₁ e₂ x ⊗ comp-REN e₁ e₂ M


𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf (\ g → Σ Nat (\ d → Terms d g n))
                         (\ { e (d , x) → d , RENS e x })
𝐑𝐄𝐍𝐒 = record
         { idℱ   = funext! (\ { (d , x) → (d ,_) & id-RENS x })
         ; compℱ = \ e₁ e₂ → funext! (\ { (d , x) → (d ,_) & comp-RENS e₁ e₂ x })
         }


comp-WKS-RENS-keep : ∀ {d g g′ n} → (e : g′ ≥ g) (x : Terms d g n)
                                  → (RENS (keep e) ∘ WKS) x ≡ (WKS ∘ RENS e) x
comp-WKS-RENS-keep e ∙       = refl
comp-WKS-RENS-keep e (x , M) = _,_ & comp-WKS-RENS-keep e x ⊗ comp-WK-REN-keep e M


comp-LIFTS-RENS : ∀ {d g g′ n} → (e : g′ ≥ g) (x : Terms d g n)
                               → (RENS (keep e) ∘ LIFTS) x ≡ (LIFTS ∘ RENS e) x
comp-LIFTS-RENS e x = (_, VZ) & comp-WKS-RENS-keep e x


--------------------------------------------------------------------------------


id-MRENS : ∀ {d g n} → (x : Terms d g n)
                     → MRENS id≥ x ≡ x
id-MRENS ∙       = refl
id-MRENS (x , M) = _,_ & id-MRENS x ⊗ id-MREN M


comp-MRENS : ∀ {d d′ d″ g n} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (x : Terms d g n)
                             → MRENS (e₁ ∘ e₂) x ≡ (MRENS e₂ ∘ MRENS e₁) x
comp-MRENS e₁ e₂ ∙       = refl
comp-MRENS e₁ e₂ (x , M) = _,_ & comp-MRENS e₁ e₂ x ⊗ comp-MREN e₁ e₂ M


𝐌𝐑𝐄𝐍𝐒 : ∀ {n} → Presheaf (\ d → Σ Nat (\ g → Terms d g n))
                          (\ { e (g , x) → g , MRENS e x })
𝐌𝐑𝐄𝐍𝐒 = record
          { idℱ   = funext! (\ { (g , x) → (g ,_) & id-MRENS x })
          ; compℱ = \ e₁ e₂ → funext! (\ { (g , x) → (g ,_) & comp-MRENS e₁ e₂ x })
          }


comp-MWKS-MRENS-drop : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms d g n)
                                    → MRENS (drop e) x ≡ (MWKS ∘ MRENS e) x
comp-MWKS-MRENS-drop e ∙       = refl
comp-MWKS-MRENS-drop e (x , M) = _,_ & comp-MWKS-MRENS-drop e x ⊗ comp-MWK-MREN-drop e M


comp-MWKS-MRENS-keep : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms d g n)
                                    → (MRENS (keep e) ∘ MWKS) x ≡ (MWKS ∘ MRENS e) x
comp-MWKS-MRENS-keep e ∙       = refl
comp-MWKS-MRENS-keep e (x , M) = _,_ & comp-MWKS-MRENS-keep e x ⊗ comp-MWK-MREN-keep e M


--------------------------------------------------------------------------------


id-MRENS₁ : ∀ {d n} → (x : Terms₁ d n)
                    → MRENS₁ id≥ x ≡ x
id-MRENS₁ x = id-MRENS x


comp-MRENS₁ : ∀ {d d′ d″ n} → (e₁ : d′ ≥ d) (e₂ : d″ ≥ d′) (x : Terms₁ d n)
                            → MRENS₁ (e₁ ∘ e₂) x ≡ (MRENS₁ e₂ ∘ MRENS₁ e₁) x
comp-MRENS₁ e₁ e₂ x = comp-MRENS e₁ e₂ x


𝐌𝐑𝐄𝐍𝐒₁ : ∀ {n} → Presheaf (flip Terms₁ n) MRENS₁
𝐌𝐑𝐄𝐍𝐒₁ = record
           { idℱ   = funext! id-MRENS₁
           ; compℱ = \ e₁ e₂ → funext! (comp-MRENS₁ e₁ e₂)
           }


comp-MWKS₁-MRENS₁-keep : ∀ {d d′ n} → (e : d′ ≥ d) (x : Terms₁ d n)
                                    → (MRENS₁ (keep e) ∘ MWKS₁) x ≡ (MWKS₁ ∘ MRENS₁ e) x
comp-MWKS₁-MRENS₁-keep e x = comp-MWKS-MRENS-keep e x


comp-MLIFTS₁-MRENS₁ : ∀ {d d′ n} → (e : d′ ≥ d) (x : Terms₁ d n)
                                 → (MRENS₁ (keep e) ∘ MLIFTS₁) x ≡ (MLIFTS₁ ∘ MRENS₁ e) x
comp-MLIFTS₁-MRENS₁ e x = (_, MVZ) & comp-MWKS₁-MRENS₁-keep e x


--------------------------------------------------------------------------------


comp-REN-GET : ∀ {d g g′ n} → (e : g′ ≥ g) (x : Terms d g n) (i : Fin n)
                            → GET (RENS e x) i ≡ (REN e ∘ GET x) i
comp-REN-GET e (x , M) zero    = refl
comp-REN-GET e (x , N) (suc i) = comp-REN-GET e x i


VAR-id-GET : ∀ {d g} → (i : Fin g)
                     → GET (IDS {d = d}) i ≡ VAR i
VAR-id-GET zero    = refl
VAR-id-GET (suc i) = comp-REN-GET (drop id≥) IDS i
                   ⋮ WK & VAR-id-GET i
                   ⋮ (\ i′ → VAR (suc i′)) & id-REN∋ i


--------------------------------------------------------------------------------


comp-MREN-GET : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms d g n) (i : Fin n)
                             → GET (MRENS e x) i ≡ (MREN e ∘ GET x) i
comp-MREN-GET e (x , M) zero    = refl
comp-MREN-GET e (x , N) (suc i) = comp-MREN-GET e x i


--------------------------------------------------------------------------------


comp-MREN-GET₁ : ∀ {d d′ n} → (e : d′ ≥ d) (x : Terms₁ d n) (i : Fin n)
                            → GET (MRENS₁ e x) i ≡ (MREN e ∘ GET x) i
comp-MREN-GET₁ e (x , M) zero    = refl
comp-MREN-GET₁ e (x , N) (suc i) = comp-MREN-GET₁ e x i


MVAR-id-GET₁ : ∀ {d} → (i : Fin d)
                     → GET MIDS₁ i ≡ MVAR i
MVAR-id-GET₁ zero    = refl
MVAR-id-GET₁ (suc i) = comp-MREN-GET₁ (drop id≥) MIDS₁ i
                     ⋮ MWK & MVAR-id-GET₁ i
                     ⋮ (\ i′ → MVAR (suc i′)) & id-REN∋ i


--------------------------------------------------------------------------------


comp-RENS-GETS : ∀ {d g g′ n n′} → (e₁ : g′ ≥ g) (x : Terms d g n′) (e₂ : n′ ≥ n)
                                 → GETS (RENS e₁ x) e₂ ≡ (RENS e₁ ∘ GETS x) e₂
comp-RENS-GETS e₁ ∙       done      = refl
comp-RENS-GETS e₁ (x , N) (drop e₂) = comp-RENS-GETS e₁ x e₂
comp-RENS-GETS e₁ (x , M) (keep e₂) = (_, REN e₁ M) & comp-RENS-GETS e₁ x e₂


comp-LIFTS-GETS : ∀ {d g n n′} → (x : Terms d g n′) (e : n′ ≥ n)
                               → GETS (LIFTS x) (keep e) ≡ (LIFTS ∘ GETS x) e
comp-LIFTS-GETS x e = (_, VZ) & comp-RENS-GETS (drop id≥) x e


--------------------------------------------------------------------------------


comp-MRENS-GETS : ∀ {d d′ g n n′} → (e₁ : d′ ≥ d) (x : Terms d g n′) (e₂ : n′ ≥ n)
                                  → GETS (MRENS e₁ x) e₂ ≡ (MRENS e₁ ∘ GETS x) e₂
comp-MRENS-GETS e₁ ∙       done      = refl
comp-MRENS-GETS e₁ (x , N) (drop e₂) = comp-MRENS-GETS e₁ x e₂
comp-MRENS-GETS e₁ (x , M) (keep e₂) = (_, MREN e₁ M) & comp-MRENS-GETS e₁ x e₂


--------------------------------------------------------------------------------


comp-MRENS₁-GETS : ∀ {d d′ n n′} → (e₁ : d′ ≥ d) (x : Terms₁ d n′) (e₂ : n′ ≥ n)
                                 → GETS (MRENS₁ e₁ x) e₂ ≡ (MRENS₁ e₁ ∘ GETS x) e₂
comp-MRENS₁-GETS e₁ x e₂ = comp-MRENS-GETS e₁ x e₂


comp-MLIFTS₁-GETS : ∀ {d n n′} → (x : Terms₁ d n′) (e : n′ ≥ n)
                               → GETS (MLIFTS₁ x) (keep e) ≡ (MLIFTS₁ ∘ GETS x) e
comp-MLIFTS₁-GETS x e = (_, MVZ) & comp-MRENS₁-GETS (drop id≥) x e


--------------------------------------------------------------------------------


comp-SUB-GET : ∀ {d g n m} → (x : Terms d g n) (y : Terms d n m) (i : Fin m)
                           → GET (SUBS x y) i ≡ (SUB x ∘ GET y) i
comp-SUB-GET x (y , M) zero    = refl
comp-SUB-GET x (y , N) (suc i) = comp-SUB-GET x y i


--------------------------------------------------------------------------------


comp-MSUB-GET : ∀ {d g n m} → (x : Terms₁ d n) (y : Terms n g m) (i : Fin m)
                            → GET (MSUBS x y) i ≡ (MSUB x ∘ GET y) i
comp-MSUB-GET x (y , M) zero    = refl
comp-MSUB-GET x (y , N) (suc i) = comp-MSUB-GET x y i


--------------------------------------------------------------------------------


comp-MSUB-GET₁ : ∀ {d n m} → (x : Terms₁ d n) (y : Terms₁ n m) (i : Fin m)
                           → GET (MSUBS₁ x y) i ≡ (MSUB x ∘ GET y) i
comp-MSUB-GET₁ x (y , M) zero    = refl
comp-MSUB-GET₁ x (y , N) (suc i) = comp-MSUB-GET₁ x y i


--------------------------------------------------------------------------------


comp-SUB-REN : ∀ {d g n n′} → (x : Terms d g n′) (e : n′ ≥ n) (M : Term d n)
                            → SUB (GETS x e) M ≡ (SUB x ∘ REN e) M
comp-SUB-REN x e (VAR i)      = comp-GET-REN∋ x e i
comp-SUB-REN x e (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-GETS x e ⁻¹
                                      ⋮ comp-SUB-REN (LIFTS x) (keep e) M
                                      )
comp-SUB-REN x e (APP M N)    = APP & comp-SUB-REN x e M ⊗ comp-SUB-REN x e N
comp-SUB-REN x e (MVAR i)     = refl
comp-SUB-REN x e (BOX M)      = refl
comp-SUB-REN x e (LETBOX M N) = LETBOX & comp-SUB-REN x e M
                                       ⊗ ( (\ x′ → SUB x′ N) & comp-MRENS-GETS (drop id≥) x e ⁻¹
                                         ⋮ comp-SUB-REN (MWKS x) e N
                                         )


--------------------------------------------------------------------------------


-- TODO: Better name?

expand-SUB : ∀ {d g n} → (x : Terms d g n) (M : Term d g) (N : Term d n)
                       → SUB (x , M) (WK N) ≡ SUB x N
expand-SUB x M N = comp-SUB-REN (x , M) (drop id≥) N ⁻¹
                 ⋮ (\ x′ → SUB x′ N) & id-GETS x


expand-SUBS : ∀ {d g n m} → (x : Terms d g n) (M : Term d g) (y : Terms d n m)
                          → SUBS (x , M) (WKS y) ≡ SUBS x y
expand-SUBS x M ∙       = refl
expand-SUBS x M (y , N) = _,_ & expand-SUBS x M y ⊗ expand-SUB x M N


--------------------------------------------------------------------------------


comp-REN-SUB : ∀ {d g g′ n} → (e : g′ ≥ g) (x : Terms d g n) (M : Term d n)
                            → SUB (RENS e x) M ≡ (REN e ∘ SUB x) M
comp-REN-SUB e x (VAR i)      = comp-REN-GET e x i
comp-REN-SUB e x (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-RENS e x ⁻¹
                                      ⋮ comp-REN-SUB (keep e) (LIFTS x) M
                                      )
comp-REN-SUB e x (APP M N)    = APP & comp-REN-SUB e x M ⊗ comp-REN-SUB e x N
comp-REN-SUB e x (MVAR i)     = refl
comp-REN-SUB e x (BOX M)      = refl
comp-REN-SUB e x (LETBOX M N) = LETBOX & comp-REN-SUB e x M
                                       ⊗ ( (\ x′ → SUB x′ N) & comp-RENS-MRENS (drop id≥) e x
                                         ⋮ comp-REN-SUB e (MWKS x) N
                                         )


comp-RENS-SUBS : ∀ {d g g′ n m} → (e : g′ ≥ g) (x : Terms d g n) (y : Terms d n m)
                                → SUBS (RENS e x) y ≡ (RENS e ∘ SUBS x) y
comp-RENS-SUBS e x ∙       = refl
comp-RENS-SUBS e x (y , M) = _,_ & comp-RENS-SUBS e x y ⊗ comp-REN-SUB e x M


comp-LIFTS-SUBS : ∀ {d g n m} → (x : Terms d g n) (y : Terms d n m)
                              → SUBS (LIFTS x) (LIFTS y) ≡ (LIFTS ∘ SUBS x) y
comp-LIFTS-SUBS x y = (_, VZ) & ( expand-SUBS (WKS x) VZ y
                                ⋮ comp-RENS-SUBS (drop id≥) x y
                                )


--------------------------------------------------------------------------------


id-MREN-SUB : ∀ {d d′ g} → (e : d′ ≥ d) (M : Term d′ g)
                         → SUB (MRENS e IDS) M ≡ M
id-MREN-SUB e (VAR i)      = comp-MREN-GET e IDS i
                           ⋮ MREN e & VAR-id-GET i
id-MREN-SUB e (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-MRENS e IDS ⁻¹
                                   ⋮ id-MREN-SUB e M
                                   )
id-MREN-SUB e (APP M N)    = APP & id-MREN-SUB e M ⊗ id-MREN-SUB e N
id-MREN-SUB e (MVAR i)     = refl
id-MREN-SUB e (BOX M)      = refl
id-MREN-SUB e (LETBOX M N) = LETBOX & id-MREN-SUB e M
                                    ⊗ ( (\ x′ → SUB x′ N) & comp-MWKS-MRENS-drop e IDS ⁻¹
                                      ⋮ id-MREN-SUB (drop e) N
                                      )


comp-MREN-SUB : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms d g n) (M : Term d n)
                             → SUB (MRENS e x) (MREN e M) ≡ (MREN e ∘ SUB x) M
comp-MREN-SUB e x (VAR i)      = comp-MREN-GET e x i
comp-MREN-SUB e x (LAM M)      = LAM & ( (\ x′ → SUB x′ (MREN e M)) & comp-LIFTS-MRENS e x ⁻¹
                                       ⋮ comp-MREN-SUB e (LIFTS x) M
                                       )
comp-MREN-SUB e x (APP M N)    = APP & comp-MREN-SUB e x M ⊗ comp-MREN-SUB e x N
comp-MREN-SUB e x (MVAR i)     = refl
comp-MREN-SUB e x (BOX M)      = refl
comp-MREN-SUB e x (LETBOX M N) = LETBOX & comp-MREN-SUB e x M
                                        ⊗ ( (\ x′ → SUB x′ (MREN (keep e) N)) & comp-MWKS-MRENS-keep e x ⁻¹
                                          ⋮ comp-MREN-SUB (keep e) (MWKS x) N
                                          )


comp-MRENS-SUBS : ∀ {d d′ g n m} → (e : d′ ≥ d) (x : Terms d g n) (y : Terms d n m)
                                 → SUBS (MRENS e x) (MRENS e y) ≡ (MRENS e ∘ SUBS x) y
comp-MRENS-SUBS e x ∙       = refl
comp-MRENS-SUBS e x (y , M) = _,_ & comp-MRENS-SUBS e x y ⊗ comp-MREN-SUB e x M


--------------------------------------------------------------------------------


id-SUB : ∀ {d g} → (M : Term d g)
                 → SUB IDS M ≡ M
id-SUB (VAR i)      = VAR-id-GET i
id-SUB (LAM M)      = LAM & id-SUB M
id-SUB (APP M N)    = APP & id-SUB M ⊗ id-SUB N
id-SUB (MVAR i)     = refl
id-SUB (BOX M)      = refl
id-SUB (LETBOX M N) = LETBOX & id-SUB M ⊗ id-MREN-SUB (drop id≥) N


comp-SUB : ∀ {d g m n} → (x : Terms d g n) (y : Terms d n m) (M : Term d m)
                       → SUB (SUBS x y) M ≡ (SUB x ∘ SUB y) M
comp-SUB x y (VAR i)      = comp-SUB-GET x y i
comp-SUB x y (LAM M)      = LAM & ( (\ x′ → SUB x′ M) & comp-LIFTS-SUBS x y ⁻¹
                                  ⋮ comp-SUB (LIFTS x) (LIFTS y) M
                                  )
comp-SUB x y (APP M N)    = APP & comp-SUB x y M ⊗ comp-SUB x y N
comp-SUB x y (MVAR i)     = refl
comp-SUB x y (BOX M)      = refl
comp-SUB x y (LETBOX M N) = LETBOX & comp-SUB x y M
                                   ⊗ ( (\ x′ → SUB x′ N) & comp-MRENS-SUBS (drop id≥) x y ⁻¹
                                     ⋮ comp-SUB (MWKS x) (MWKS y) N
                                     )


lid-SUBS : ∀ {d g n} → (x : Terms d g n)
                     → SUBS IDS x ≡ x
lid-SUBS ∙       = refl
lid-SUBS (x , M) = _,_ & lid-SUBS x ⊗ id-SUB M


rid-SUBS : ∀ {d g n} → (x : Terms d g n)
                     → SUBS x IDS ≡ x
rid-SUBS ∙       = refl
rid-SUBS (x , M) = (_, M) & ( expand-SUBS x M IDS
                            ⋮ rid-SUBS x
                            )


assoc-SUBS : ∀ {d g n m o} → (x : Terms d g n) (y : Terms d n m) (z : Terms d m o)
                           → SUBS (SUBS x y) z ≡ SUBS x (SUBS y z)
assoc-SUBS x y ∙       = refl
assoc-SUBS x y (z , M) = _,_ & assoc-SUBS x y z ⊗ comp-SUB x y M


instance
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬 : ∀ {d} → Category Nat (Terms d)
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬 = record
              { id     = IDS
              ; _∘_    = flip SUBS
              ; lid∘   = rid-SUBS
              ; rid∘   = lid-SUBS
              ; assoc∘ = \ z y x → assoc-SUBS x y z ⁻¹
              }


𝐒𝐔𝐁 : ∀ {d} → Presheaf (Term d) SUB
𝐒𝐔𝐁 = record
        { idℱ   = funext! id-SUB
        ; compℱ = \ y x → funext! (comp-SUB x y)
        }


--------------------------------------------------------------------------------


comp-MSUB-REN : ∀ {d g g′ n} → (x : Terms₁ d n) (e : g′ ≥ g) (M : Term n g)
                             → (REN e ∘ MSUB x) M ≡ (MSUB x ∘ REN e) M
comp-MSUB-REN x e (VAR i)      = refl
comp-MSUB-REN x e (LAM M)      = LAM & comp-MSUB-REN x (keep e) M
comp-MSUB-REN x e (APP M N)    = APP & comp-MSUB-REN x e M ⊗ comp-MSUB-REN x e N
comp-MSUB-REN x e (MVAR i)     = comp-REN-SUB e ∙ (GET x i) ⁻¹
comp-MSUB-REN x e (BOX M)      = refl
comp-MSUB-REN x e (LETBOX M N) = LETBOX & comp-MSUB-REN x e M ⊗ comp-MSUB-REN (MLIFTS₁ x) e N


comp-MSUBS-RENS : ∀ {d g g′ n m} → (x : Terms₁ d n) (e : g′ ≥ g) (y : Terms n g m)
                                 → (RENS e ∘ MSUBS x) y ≡ (MSUBS x ∘ RENS e) y
comp-MSUBS-RENS x e ∙       = refl
comp-MSUBS-RENS x e (y , M) = _,_ & comp-MSUBS-RENS x e y ⊗ comp-MSUB-REN x e M


comp-MSUBS-LIFTS : ∀ {d g n m} → (x : Terms₁ d n) (y : Terms n g m)
                               → (LIFTS ∘ MSUBS x) y ≡ (MSUBS x ∘ LIFTS) y
comp-MSUBS-LIFTS x y = (_, VZ) & comp-MSUBS-RENS x (drop id≥) y


--------------------------------------------------------------------------------


comp-MSUB-MREN : ∀ {d g n n′} → (x : Terms₁ d n′) (e : n′ ≥ n) (M : Term n g)
                              → MSUB (GETS x e) M ≡ (MSUB x ∘ MREN e) M
comp-MSUB-MREN x e (VAR i)      = refl
comp-MSUB-MREN x e (LAM M)      = LAM & comp-MSUB-MREN x e M
comp-MSUB-MREN x e (APP M N)    = APP & comp-MSUB-MREN x e M ⊗ comp-MSUB-MREN x e N
comp-MSUB-MREN x e (MVAR i)     = SUB ∙ & comp-GET-REN∋ x e i
comp-MSUB-MREN x e (BOX M)      = BOX & comp-MSUB-MREN x e M
comp-MSUB-MREN x e (LETBOX M N) = LETBOX & comp-MSUB-MREN x e M
                                         ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS₁-GETS x e ⁻¹
                                           ⋮ comp-MSUB-MREN (MLIFTS₁ x) (keep e) N
                                           )


--------------------------------------------------------------------------------


-- TODO: Better name?

expand-MSUB : ∀ {d g n} → (x : Terms₁ d n) (M : Term₁ d) (N : Term n g)
                        → MSUB (x , M) (MWK N) ≡ MSUB x N
expand-MSUB x M N = comp-MSUB-MREN (x , M) (drop id≥) N ⁻¹
                  ⋮ (\ x′ → MSUB x′ N) & id-GETS x


expand-MSUBS : ∀ {d g n m} → (x : Terms₁ d n) (M : Term₁ d) (y : Terms n g m)
                           → MSUBS (x , M) (MWKS y) ≡ MSUBS x y
expand-MSUBS x M ∙       = refl
expand-MSUBS x M (y , N) = _,_ & expand-MSUBS x M y ⊗ expand-MSUB x M N


expand-MSUBS₁ : ∀ {d n m} → (x : Terms₁ d n) (M : Term₁ d) (y : Terms₁ n m)
                          → MSUBS₁ (x , M) (MWKS₁ y) ≡ MSUBS₁ x y
expand-MSUBS₁ x M y = expand-MSUBS x M y


--------------------------------------------------------------------------------


comp-MREN-MSUB : ∀ {d d′ g n} → (e : d′ ≥ d) (x : Terms₁ d n) (M : Term n g)
                              → MSUB (MRENS₁ e x) M ≡ (MREN e ∘ MSUB x) M
comp-MREN-MSUB e x (VAR i)      = refl
comp-MREN-MSUB e x (LAM M)      = LAM & comp-MREN-MSUB e x M
comp-MREN-MSUB e x (APP M N)    = APP & comp-MREN-MSUB e x M ⊗ comp-MREN-MSUB e x N
comp-MREN-MSUB e x (MVAR i)     = SUB ∙ & comp-MREN-GET₁ e x i
                                ⋮ comp-MREN-SUB e ∙ (GET x i)
comp-MREN-MSUB e x (BOX M)      = BOX & comp-MREN-MSUB e x M
comp-MREN-MSUB e x (LETBOX M N) = LETBOX & comp-MREN-MSUB e x M
                                         ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS₁-MRENS₁ e x ⁻¹
                                           ⋮ comp-MREN-MSUB (keep e) (MLIFTS₁ x) N
                                           )


comp-MRENS-MSUBS : ∀ {d d′ g n m} → (e : d′ ≥ d) (x : Terms₁ d n) (y : Terms n g m)
                                  → MSUBS (MRENS₁ e x) y ≡ (MRENS e ∘ MSUBS x) y
comp-MRENS-MSUBS e x ∙       = refl
comp-MRENS-MSUBS e x (y , M) = _,_ & comp-MRENS-MSUBS e x y ⊗ comp-MREN-MSUB e x M


comp-MWKS-MSUBS : ∀ {d g n m} → (x : Terms₁ d n) (y : Terms n g m)
                              → (MSUBS (MLIFTS₁ x) ∘ MWKS) y ≡ (MWKS ∘ MSUBS x) y
comp-MWKS-MSUBS x y = expand-MSUBS (MWKS₁ x) MVZ y
                    ⋮ comp-MRENS-MSUBS (drop id≥) x y


comp-MRENS₁-MSUBS₁ : ∀ {d d′ n m} → (e : d′ ≥ d) (x : Terms₁ d n) (y : Terms₁ n m)
                                  → MSUBS₁ (MRENS₁ e x) y ≡ (MRENS₁ e ∘ MSUBS₁ x) y
comp-MRENS₁-MSUBS₁ e x y = comp-MRENS-MSUBS e x y


comp-MWKS₁-MSUBS₁ : ∀ {d n m} → (x : Terms₁ d n) (y : Terms₁ n m)
                              → (MSUBS₁ (MLIFTS₁ x) ∘ MWKS₁) y ≡ (MWKS₁ ∘ MSUBS₁ x) y
comp-MWKS₁-MSUBS₁ x y = expand-MSUBS₁ (MWKS₁ x) MVZ y
                      ⋮ comp-MRENS₁-MSUBS₁ (drop id≥) x y


comp-MLIFTS₁-MSUBS₁ : ∀ {d n m} → (x : Terms₁ d n) (y : Terms₁ n m)
                                → (MSUBS₁ (MLIFTS₁ x) ∘ MLIFTS₁) y ≡ (MLIFTS₁ ∘ MSUBS₁ x) y
comp-MLIFTS₁-MSUBS₁ x y = (_, MVZ) & comp-MWKS₁-MSUBS₁ x y


--------------------------------------------------------------------------------


comp-MSUB-SUB : ∀ {d g n m} → (x : Terms₁ d n) (y : Terms n g m) (M : Term n m)
                            → (SUB (MSUBS x y) ∘ MSUB x) M ≡ (MSUB x ∘ SUB y) M
comp-MSUB-SUB x y (VAR i)      = comp-MSUB-GET x y i
comp-MSUB-SUB x y (LAM M)      = LAM & ( (\ x′ → SUB x′ (MSUB x M)) & comp-MSUBS-LIFTS x y
                                       ⋮ comp-MSUB-SUB x (LIFTS y) M
                                       )
comp-MSUB-SUB x y (APP M N)    = APP & comp-MSUB-SUB x y M ⊗ comp-MSUB-SUB x y N
comp-MSUB-SUB x y (MVAR i)     = comp-SUB (MSUBS x y) ∙ (GET x i) ⁻¹
comp-MSUB-SUB x y (BOX M)      = refl
comp-MSUB-SUB x y (LETBOX M N) = LETBOX & comp-MSUB-SUB x y M
                                        ⊗ ( (\ x′ → SUB x′ (MSUB (MWKS₁ x , MVZ) N)) & comp-MWKS-MSUBS x y ⁻¹
                                          ⋮ comp-MSUB-SUB (MLIFTS₁ x) (MWKS y) N
                                          )


--------------------------------------------------------------------------------


id-MSUB : ∀ {d g} → (M : Term d g)
                  → MSUB MIDS₁ M ≡ M
id-MSUB (VAR i)      = refl
id-MSUB (LAM M)      = LAM & id-MSUB M
id-MSUB (APP M N)    = APP & id-MSUB M ⊗ id-MSUB N
id-MSUB (MVAR i)     = SUB ∙ & MVAR-id-GET₁ i
id-MSUB (BOX M)      = BOX & id-MSUB M
id-MSUB (LETBOX M N) = LETBOX & id-MSUB M ⊗ id-MSUB N


comp-MSUB : ∀ {d g n m} → (x : Terms₁ d n) (y : Terms₁ n m) (M : Term m g)
                        → MSUB (MSUBS₁ x y) M ≡ (MSUB x ∘ MSUB y) M
comp-MSUB x y (VAR i)      = refl
comp-MSUB x y (LAM M)      = LAM & comp-MSUB x y M
comp-MSUB x y (APP M N)    = APP & comp-MSUB x y M ⊗ comp-MSUB x y N
comp-MSUB x y (MVAR i)     = SUB ∙ & comp-MSUB-GET₁ x y i
                           ⋮ comp-MSUB-SUB x ∙ (GET y i)
comp-MSUB x y (BOX M)      = BOX & comp-MSUB x y M
comp-MSUB x y (LETBOX M N) = LETBOX & comp-MSUB x y M
                                    ⊗ ( (\ x′ → MSUB x′ N) & comp-MLIFTS₁-MSUBS₁ x y ⁻¹
                                      ⋮ comp-MSUB (MLIFTS₁ x) (MLIFTS₁ y) N
                                      )


lid-MSUBS₁ : ∀ {d n} → (x : Terms₁ d n)
                     → MSUBS₁ MIDS₁ x ≡ x
lid-MSUBS₁ ∙       = refl
lid-MSUBS₁ (x , M) = _,_ & lid-MSUBS₁ x ⊗ id-MSUB M


rid-MSUBS₁ : ∀ {d n} → (x : Terms₁ d n)
                     → MSUBS₁ x MIDS₁ ≡ x
rid-MSUBS₁ ∙       = refl
rid-MSUBS₁ (x , M) = _,_ & ( expand-MSUBS₁ x M MIDS₁
                           ⋮ rid-MSUBS₁ x
                           )
                         ⊗ id-SUB M


assoc-MSUBS₁ : ∀ {d n m o} → (x : Terms₁ d n) (y : Terms₁ n m) (z : Terms₁ m o)
                           → MSUBS₁ (MSUBS₁ x y) z ≡ MSUBS₁ x (MSUBS₁ y z)
assoc-MSUBS₁ x y ∙       = refl
assoc-MSUBS₁ x y (z , M) = _,_ & assoc-MSUBS₁ x y z ⊗ comp-MSUB x y M


instance
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬₁ : Category Nat Terms₁
  𝐒𝟒𝐓𝐞𝐫𝐦𝐬₁ = record
               { id     = MIDS₁
               ; _∘_    = flip MSUBS₁
               ; lid∘   = rid-MSUBS₁
               ; rid∘   = lid-MSUBS₁
               ; assoc∘ = \ z y x → assoc-MSUBS₁ x y z ⁻¹
               }


𝐌𝐒𝐔𝐁 : Presheaf Term₁ MSUB
𝐌𝐒𝐔𝐁 = record
         { idℱ   = funext! id-MSUB
         ; compℱ = \ y x → funext! (comp-MSUB x y)
         }


--------------------------------------------------------------------------------
