module Kit2 where

open import Kit1 public
open ≡-Reasoning


----------------------------------------------------------------------------------------------------

record RenSubKit1Params : Set₁ where
  constructor kit
  field
    subkit : SubKitParams
  open SubKitParams subkit public
  open SubKit subkit public hiding (subkit)
  field
    lidren  : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
    compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
              ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t
    --        ren (e ○ e′) t ≡ (ren e′ ∘ ren e) t
    ridren  : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
    ridsub  : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i

module RenSubKit1 (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  rensubkit1 = ¶

  lidren* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
            ren* id⊆ ts ≡ ts
  --        ts ◐ id⊆ ≡ ts
  lidren* []       = refl
  lidren* (t ∷ ts) = _∷_ & lidren t ⊗ lidren* ts

  -- Kovacs: assₛₑₑ
  compren* : ∀ {Γ Γ′ Γ″ Δ} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             ren* (e′ ∘⊆ e) ts ≡ (ren* e′ ∘ ren* e) ts
  --         ts ◐ (e ○ e′) ≡ (ts ◐ e) ◐ e′
  compren* e′ e []       = refl
  compren* e′ e (t ∷ ts) = _∷_ & compren e′ e t ⊗ compren* e′ e ts

  eqwkren : ∀ {B Γ Γ′ A} (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            (ren (lift⊆ e) ∘ wk) t ≡ (wk {B} ∘ ren e) t
  eqwkren e t = compren (lift⊆ e) (wk⊆ id⊆) t ⁻¹
              ⋮ (flip ren t ∘ wk⊆) & (rid⊆ e ⋮ lid⊆ e ⁻¹)
              ⋮ compren (wk⊆ id⊆) e t

  eqwkren* : ∀ {B Γ Γ′ Δ} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             (ren* (lift⊆ e) ∘ wk*) ts ≡ (wk* {B} ∘ ren* e) ts
  --         (wk* ts) ◐ (lift⊆ e) ≡ wk* {B} (ts ◐ e)
  eqwkren* e []       = refl
  eqwkren* e (t ∷ ts) = _∷_ & eqwkren e t ⊗ eqwkren* e ts

  -- TODO: inline?
  eqwk²ren* : ∀ {B₁ B₂ Γ Γ′ Δ} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
              (ren* (lift⊆² e) ∘ (wk* ∘ wk*)) ts ≡ ((wk* {B₁} ∘ wk* {B₂}) ∘ ren* e) ts
  eqwk²ren* e ts = eqwkren* (lift⊆ e) (wk* ts) ⋮ wk* & eqwkren* e ts

  eqliftren* : ∀ {B Γ Γ′ Δ} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
               (ren* (lift⊆ e) ∘ lift*) ts ≡ (lift* {B} ∘ ren* e) ts
  --           (lift* ts) ◐ (lift⊆ e) ≡ lift* {B} (ts ◐ e)
  eqliftren* e ts = (_∷ (ren* (lift⊆ e) ∘ wk*) ts) & ridren (lift⊆ e) zero
                  ⋮ (var zero ∷_) & eqwkren* e ts

  -- Kovacs: idlₛₑ; not really identity
  ridren* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) →
            ren* e id* ≡ var* e
  --        id* ◐ e ≡ var* e
  ridren* stop⊆     = refl
  ridren* (wk⊆ e)   = (flip ren* id* ∘ wk⊆) & lid⊆ e ⁻¹
                    ⋮ compren* (wk⊆ id⊆) e id*
                    ⋮ wk* & ridren* e
  ridren* (lift⊆ e) = (_∷ (ren* (lift⊆ e) ∘ wk*) id*) & ridren (lift⊆ e) zero
                    ⋮ (var zero ∷_) & (eqwkren* e id* ⋮ wk* & ridren* e)

  -- Kovacs: ∈-ₛ∘ₑa
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
              sub∋ (ren* e ss) i ≡ (ren e ∘ sub∋ ss) i
  --          sub∋ (ss ◐ e) i ≡ (sub∋ ss ⨾ ren e) i
  eqrensub∋ e (s ∷ ss) zero    = refl
  eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
              sub∋ (get* e ss) i ≡ (sub∋ ss ∘ ren∋ e) i
  --          sub∋ (e ◑ ss) i ≡ (ren∋ e ⨾ sub∋ ss) i
  eqsubren∋ []       stop⊆     i       = refl
  eqsubren∋ (s ∷ ss) (wk⊆ e)   i       = eqsubren∋ ss e i
  eqsubren∋ (s ∷ ss) (lift⊆ e) zero    = refl
  eqsubren∋ (s ∷ ss) (lift⊆ e) (suc i) = eqsubren∋ ss e i

  -- Kovacs: ∈-idₛ; not really identity
  idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ id* i ≡ var i
  idsub∋ zero    = refl
  idsub∋ (suc i) = eqrensub∋ (wk⊆ id⊆) id* i
                 ⋮ wk & idsub∋ i
                 ⋮ ridren (wk⊆ id⊆) i
                 ⋮ (var ∘ suc) & idren∋ i

  -- Kovacs: ∈-∘ₛ; not really composition
  compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
             sub∋ (sub* ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
  --         sub∋ (ss ● ss′) i ≡ (sub∋ ss ⨾ sub ss′) i
  compsub∋ ss′ (s ∷ ss) zero    = refl
  compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i

  -- Kovacs: idlₑₛ
  lidget* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
            get* id⊆ ts ≡ ts
  --        id⊆ ◑ ts ≡ ts
  lidget* []       = refl
  lidget* (t ∷ ts) = (t ∷_) & lidget* ts

  compget* : ∀ {Γ Δ Δ′ Δ″} (e : Δ ⊆ Δ′) (e′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
             get* (e′ ∘⊆ e) ts ≡ (get* e ∘ get* e′) ts
  --         (e ○ e′) ◑ ts ≡ e ◑ (e′ ◑ ts)
  compget* e         stop⊆      []       = refl
  compget* e         (wk⊆ e′)   (t ∷ ts) = compget* e e′ ts
  compget* (wk⊆ e)   (lift⊆ e′) (t ∷ ts) = compget* e e′ ts
  compget* (lift⊆ e) (lift⊆ e′) (t ∷ ts) = (t ∷_) & compget* e e′ ts

  -- Kovacs: assₑₛₑ
  eqrenget* : ∀ {Γ Γ′ Δ Δ′} (e : Γ ⊆ Γ′) (e′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
              (get* e′ ∘ ren* e) ts ≡ (ren* e ∘ get* e′) ts
  --          e′ ◑ (ts ◐ e) ≡ (e′ ◑ ts) ◐ e
  eqrenget* e stop⊆      []       = refl
  eqrenget* e (wk⊆ e′)   (t ∷ ts) = eqrenget* e e′ ts
  eqrenget* e (lift⊆ e′) (t ∷ ts) = (ren e t ∷_) & eqrenget* e e′ ts

  eqwkget* : ∀ {B Γ Δ Δ′} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
             (get* (wk⊆ e) ∘ lift*) ts ≡ (wk* {B} ∘ get* e) ts
  --         (wk⊆ e) ◑ (lift* ts) ≡ wk* {B} (e ◑ ts)
  eqwkget* e ts = eqrenget* (wk⊆ id⊆) e ts

  eqliftget* : ∀ {B Γ Δ Δ′} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
               (get* (lift⊆ e) ∘ lift*) ts ≡ (lift* {B} ∘ get* e) ts
  --           (lift⊆ e) ◑ (lift* ts) ≡ lift* {B} (e ◑ ts)
  eqliftget* e ts = (var zero ∷_) & eqwkget* e ts

  -- Kovacs: idrₑₛ; not really identity
  ridget* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) →
            get* e id* ≡ var* e
  --        e ◑ id* ≡ var* e
  ridget* stop⊆     = refl
  ridget* (wk⊆ e)   = eqrenget* (wk⊆ id⊆) e id* ⋮ wk* & ridget* e
  ridget* (lift⊆ e) = (var zero ∷_) & (eqrenget* (wk⊆ id⊆) e id* ⋮ wk* & ridget* e)


----------------------------------------------------------------------------------------------------

record RenSubKit2Params : Set₁ where
  constructor kit
  field
    rensubkit1 : RenSubKit1Params
  open RenSubKit1Params rensubkit1 public
  open RenSubKit1 rensubkit1 public hiding (rensubkit1)
  field
    eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
               sub (ren* e ss) t ≡ (ren e ∘ sub ss) t
    --         sub (ss ◐ e) t ≡ (sub ss ⨾ ren e) t
    eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
               sub (get* e ss) t ≡ (sub ss ∘ ren e) t
    --         sub (e ◑ ss) t ≡ (ren e ⨾ sub ss) t
    lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub id* t ≡ t

module RenSubKit2 (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  rensubkit2 = ¶

  -- Kovacs: assₛₛₑ
  eqrensub* : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
              sub* (ren* e ss) ts ≡ (ren* e ∘ sub* ss) ts
  --          ts ● (ss ◐ e) ≡ (ts ● ss) ◐ e
  eqrensub* e ss []       = refl
  eqrensub* e ss (t ∷ ts) = _∷_ & eqrensub e ss t ⊗ eqrensub* e ss ts

  -- Kovacs: assₛₑₛ
  eqsubren* : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
              sub* (get* e ss) ts ≡ (sub* ss ∘ ren* e) ts
  --          ts ● (e ◑ ss) ≡ (ts ◐ e) ● ss
  eqsubren* ss e []       = refl
  eqsubren* ss e (t ∷ ts) = _∷_ & eqsubren ss e t ⊗ eqsubren* ss e ts

  -- Kovacs: idrₛ
  lidsub* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
            sub* id* ts ≡ ts
  --        ts ● id* ≡ ts
  lidsub* []       = refl
  lidsub* (t ∷ ts) = _∷_ & lidsub t ⊗ lidsub* ts

  eqsub : ∀ {B Γ Ξ A} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          (sub (s ∷ ss) ∘ wk) t ≡ sub ss t
  eqsub s ss t = eqsubren (s ∷ ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & lidget* ss

  eqwksub : ∀ {B Γ Ξ A} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            (sub (lift* ss) ∘ wk) t ≡ (wk {B} ∘ sub ss) t
  eqwksub ss t = eqsubren (lift* ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & (eqwkget* id⊆ ss ⋮ wk* & lidget* ss)
               ⋮ eqrensub (wk⊆ id⊆) ss t

  eqsub* : ∀ {B Γ Ξ Δ} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
           (sub* (s ∷ ss) ∘ wk*) ts ≡ sub* ss ts
  --       (wk* ts) ● (s ∷ ss) ≡ ts ● ss
  eqsub* s ss []       = refl
  eqsub* s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsub* s ss ts

  eqwksub* : ∀ {B Γ Ξ Δ} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             (sub* (lift* ss) ∘ wk*) ts ≡ (wk* {B} ∘ sub* ss) ts
  --         (wk* ts) ● (lift* ss) ≡ wk* {B} (ts ● ss)
  eqwksub* ss []       = refl
  eqwksub* ss (t ∷ ts) = _∷_ & eqwksub ss t ⊗ eqwksub* ss ts

  eqliftsub* : ∀ {B Γ Ξ Δ} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
               (sub* (lift* ss) ∘ lift*) ts ≡ (lift* {B} ∘ sub* ss) ts
  --           (lift* ts) ● (lift* ss) ≡ lift* {B} (ts ● ss)
  eqliftsub* ss ts = (_∷ (sub* (lift* ss) ∘ wk*) ts) & ridsub (lift* ss) zero
                   ⋮ (var zero ∷_) & eqwksub* ss ts

  -- Kovacs: idlₛ
  ridsub* : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) →
            sub* ss id* ≡ ss
  --        id* ● ss ≡ ss
  ridsub* []       = refl
  ridsub* (s ∷ ss) = (_∷ (sub* (s ∷ ss) ∘ wk*) id*) & ridsub (s ∷ ss) zero
                   ⋮ (s ∷_) & (eqsub* s ss id* ⋮ ridsub* ss)


----------------------------------------------------------------------------------------------------

record RenSubKit3Params : Set₁ where
  constructor kit
  field
    rensubkit2 : RenSubKit2Params
  open RenSubKit2Params rensubkit2 public
  open RenSubKit2 rensubkit2 public hiding (rensubkit2)
  field
    compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
              sub (sub* ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
    --        sub (ss ● ss′) t ≡ (sub ss ⨾ sub ss′) t

module RenSubKit3 (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  rensubkit3 = ¶

  -- Kovacs: assₛ
  asssub* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
            (sub* ss′ ∘ sub* ss) ts ≡ sub* (sub* ss′ ss) ts
  --        (ts ● ss) ● ss′ ≡ ts ● (ss ● ss′)
  asssub* ss′ ss []       = refl
  asssub* ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⁻¹ ⊗ asssub* ss′ ss ts

  rencut : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           ren (lift⊆ e) t₁ [ ren e t₂ ] ≡ ren e (t₁ [ t₂ ])
  rencut e t₁ t₂ = eqsubren (ren e t₂ ∷ id*) (lift⊆ e) t₁ ⁻¹
                 ⋮ (flip sub t₁ ∘ (ren e t₂ ∷_)) & (ridget* e ⋮ ridren* e ⁻¹)
                 ⋮ eqrensub e (t₂ ∷ id*) t₁

  subcut : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           sub (lift* ss) t₁ [ sub ss t₂ ] ≡ sub ss (t₁ [ t₂ ])
  subcut ss t₁ t₂ = compsub (sub ss t₂ ∷ id*) (lift* ss) t₁ ⁻¹
                  ⋮ (flip sub t₁ ∘ (_∷ (sub* (sub ss t₂ ∷ id*) ∘ wk*) ss)) &
                      ridsub (sub ss t₂ ∷ id*) zero
                  ⋮ (flip sub t₁ ∘ (sub ss t₂ ∷_)) &
                      ( eqsubren* (sub ss t₂ ∷ id*) (wk⊆ id⊆) ss ⁻¹
                      ⋮ flip sub* ss & lidget* id*
                      ⋮ lidsub* ss
                      ⋮ ridsub* ss ⁻¹
                      )
                  ⋮ compsub ss (t₂ ∷ id*) t₁


----------------------------------------------------------------------------------------------------
