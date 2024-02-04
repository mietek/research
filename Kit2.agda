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
    ridren  : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
    lidren  : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)

    -- -- like compsub
    -- compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
    -- --        sub (sub* ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
    --           sub (ss ● ss′) t ≡ (sub ss ⨾ sub ss′) t
    compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
    --        ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t
              ren (e ○ e′) t ≡ (ren e ⨾ ren e′) t

module RenSubKit1 (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  rensubkit1 = ¶

  ridren* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
  --        ren* id⊆ ts ≡ ts
            ts ◐ id⊆ ≡ ts
  ridren* []       = refl
  ridren* (t ∷ ts) = _∷_ & ridren t ⊗ ridren* ts

  -- Kovacs: assₛₑₑ
  compren* : ∀ {Γ Γ′ Γ″ Δ} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
  --         ren* (e′ ∘⊆ e) ts ≡ (ren* e′ ∘ ren* e) ts
             ts ◐ (e ○ e′) ≡ (ts ◐ e) ◐ e′
  compren* e′ e []       = refl
  compren* e′ e (t ∷ ts) = _∷_ & compren e′ e t ⊗ compren* e′ e ts

  eqwkren : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            (ren (lift⊆ e) ∘ wk) t ≡ (wk ∘ ren e) t :> (B ∷ Γ′ ⊢ A)
  eqwkren e t = compren (lift⊆ e) (wk⊆ id⊆) t ⁻¹
              ⋮ (flip ren t ∘ wk⊆) & (lid⊆ e ⋮ rid⊆ e ⁻¹)
              ⋮ compren (wk⊆ id⊆) e t

  eqwkren* : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
  --         (ren* (lift⊆ {A = B} e) ∘ wk*) ts ≡ (wk* ∘ ren* e) ts
             (wk* ts) ◐ (lift⊆ e) ≡ wk* (ts ◐ e) :> (B ∷ Γ′ ⊢* Δ)
  eqwkren* e []       = refl
  eqwkren* e (t ∷ ts) = _∷_ & eqwkren e t ⊗ eqwkren* e ts

  eqliftren* : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
  --           (ren* (lift⊆ {A = B} e) ∘ lift*) ts ≡ (lift* ∘ ren* e) ts
               (lift* ts) ◐ (lift⊆ {A = B} e) ≡ lift* (ts ◐ e)
  eqliftren* e ts = (_∷ (ren* (lift⊆ e) ∘ wk*) ts) & lidren (lift⊆ e) zero
                  ⋮ (var zero ∷_) & eqwkren* e ts

  -- Kovacs: idlₛₑ; not really identity
  lidren* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) →
  --        ren* e id* ≡ var* e
            id* ◐ e ≡ var* e
  lidren* stop⊆     = refl
  lidren* (wk⊆ e)   = (flip ren* id* ∘ wk⊆) & rid⊆ e ⁻¹
                    ⋮ compren* (wk⊆ id⊆) e id*
                    ⋮ wk* & lidren* e
  lidren* (lift⊆ e) = (_∷ (ren* (lift⊆ e) ∘ wk*) id*) & lidren (lift⊆ e) zero
                    ⋮ (var zero ∷_) & (eqwkren* e id* ⋮ wk* & lidren* e)

  module _ (⚠ : FunExt) where
    ⟪ren⟫ : ∀ (A : Ty) → Presheaf ⟪⊇⟫ lzero
    ⟪ren⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = ren
                ; idƒ  = ⚠ ridren
                ; _∘ƒ_ = λ e′ e → ⚠ (compren e′ e)
                }

    -- TODO: did Kovacs find this presheaf?
    ⟪ren*⟫ : ∀ (Δ : Ctx) → Presheaf ⟪⊇⟫ lzero
    ⟪ren*⟫ Δ = record
                 { ƒObj = _⊢* Δ
                 ; ƒ    = flip _◐_ -- ren*
                 ; idƒ  = ⚠ ridren*
                 ; _∘ƒ_ = λ e′ e → ⚠ (compren* e′ e)
                 }

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
  --          sub∋ (get* e ss) i ≡ (sub∋ ss ∘ ren∋ e) i
              sub∋ (e ◑ ss) i ≡ (ren∋ e ⨾ sub∋ ss) i
  eqsubren∋ []       stop⊆     i       = refl
  eqsubren∋ (s ∷ ss) (wk⊆ e)   i       = eqsubren∋ ss e i
  eqsubren∋ (s ∷ ss) (lift⊆ e) zero    = refl
  eqsubren∋ (s ∷ ss) (lift⊆ e) (suc i) = eqsubren∋ ss e i

  -- Kovacs: idlₑₛ
  lidget* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
  --        get* id⊆ ts ≡ ts
            id⊆ ◑ ts ≡ ts
  lidget* []       = refl
  lidget* (t ∷ ts) = (t ∷_) & lidget* ts

  compget* : ∀ {Γ Δ Δ′ Δ″} (e : Δ ⊆ Δ′) (e′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
  --           get* (e′ ∘⊆ e) ts ≡ (get* e ∘ get* e′) ts
             (e ○ e′) ◑ ts ≡ e ◑ (e′ ◑ ts)
  compget* e         stop⊆      []       = refl
  compget* e         (wk⊆ e′)   (t ∷ ts) = compget* e e′ ts
  compget* (wk⊆ e)   (lift⊆ e′) (t ∷ ts) = compget* e e′ ts
  compget* (lift⊆ e) (lift⊆ e′) (t ∷ ts) = (t ∷_) & compget* e e′ ts

  -- Kovacs: assₑₛₑ
  eqrenget* : ∀ {Γ Γ′ Δ Δ′} (e : Γ ⊆ Γ′) (e′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
  --          (get* e′ ∘ ren* e) ts ≡ (ren* e ∘ get* e′) ts
              e′ ◑ (ts ◐ e) ≡ (e′ ◑ ts) ◐ e
  eqrenget* e stop⊆      []       = refl
  eqrenget* e (wk⊆ e′)   (t ∷ ts) = eqrenget* e e′ ts
  eqrenget* e (lift⊆ e′) (t ∷ ts) = (ren e t ∷_) & eqrenget* e e′ ts

  eqliftget* : ∀ {Γ Δ Δ′ B} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
  --           (get* (lift⊆ {A = B} e) ∘ lift*) ts ≡ (lift* ∘ get* e) ts
             (lift⊆ {A = B} e) ◑ (lift* ts) ≡ lift* (e ◑ ts)
  eqliftget* e ts = (var zero ∷_) & eqrenget* (wk⊆ id⊆) e ts

  -- Kovacs: idrₑₛ; not really identity
  ridget* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) →
  --        get* e id* ≡ var* e
            e ◑ id* ≡ var* e
  ridget* stop⊆     = refl
  ridget* (wk⊆ e)   = eqrenget* (wk⊆ id⊆) e id* ⋮ wk* & ridget* e
  ridget* (lift⊆ e) = (var zero ∷_) & (eqrenget* (wk⊆ id⊆) e id* ⋮ wk* & ridget* e)

  module _ (⚠ : FunExt) where
    -- TODO: did Kovacs find this presheaf?
    ⟪get*⟫ : ∀ (Γ : Ctx) → Presheaf (⟪⊇⟫ ᵒᵖ) lzero
    ⟪get*⟫ Γ = record
                 { ƒObj = Γ ⊢*_
                 ; ƒ    = _◑_ -- get*
                 ; idƒ  = ⚠ lidget*
                 ; _∘ƒ_ = λ e e′ → ⚠ (compget* e e′)
                 }

  -- Kovacs: ∈-ₛ∘ₑa
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
  --          sub∋ (ren* e ss) i ≡ (ren e ∘ sub∋ ss) i
              sub∋ (ss ◐ e) i ≡ (sub∋ ss ⨾ ren e) i
  eqrensub∋ e (s ∷ ss) zero    = refl
  eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

  -- Kovacs: ∈-idₛ; not really identity
  idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ id* i ≡ var i
  idsub∋ zero    = refl
  idsub∋ (suc i) = eqrensub∋ (wk⊆ id⊆) id* i
                 ⋮ wk & idsub∋ i
                 ⋮ lidren (wk⊆ id⊆) i
                 ⋮ (var ∘ suc) & idren∋ i

  -- Kovacs: ∈-∘ₛ; not really composition
  compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
  --         sub∋ (sub* ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
             sub∋ (ss ● ss′) i ≡ (sub∋ ss ⨾ sub ss′) i
  compsub∋ ss′ (s ∷ ss) zero    = refl
  compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i


----------------------------------------------------------------------------------------------------

record RenSubKit2Params : Set₁ where
  constructor kit
  field
    rensubkit1 : RenSubKit1Params
  open RenSubKit1Params rensubkit1 public
  open RenSubKit1 rensubkit1 public hiding (rensubkit1)
  field
    eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
    --         sub (get* e ss) t ≡ (sub ss ∘ ren e) t
               sub (e ◑ ss) t ≡ (ren e ⨾ sub ss) t
    eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
    --         sub (ren* e ss) t ≡ (ren e ∘ sub ss) t
               sub (ss ◐ e) t ≡ (sub ss ⨾ ren e) t
    ridsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub id* t ≡ t
    lidsub   : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i

module RenSubKit2 (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  rensubkit2 = ¶

  -- Kovacs: assₛₑₛ
  eqsubren* : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
  --          sub* (get* e ss) ts ≡ (sub* ss ∘ ren* e) ts
              ts ● (e ◑ ss) ≡ (ts ◐ e) ● ss
  eqsubren* ss e []       = refl
  eqsubren* ss e (t ∷ ts) = _∷_ & eqsubren ss e t ⊗ eqsubren* ss e ts

  -- Kovacs: assₛₛₑ
  eqrensub* : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  --          sub* (ren* e ss) ts ≡ (ren* e ∘ sub* ss) ts
              ts ● (ss ◐ e) ≡ (ts ● ss) ◐ e
  eqrensub* e ss []       = refl
  eqrensub* e ss (t ∷ ts) = _∷_ & eqrensub e ss t ⊗ eqrensub* e ss ts

  -- Kovacs: idrₛ
  ridsub* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
  --        sub* id* ts ≡ ts
            ts ● id* ≡ ts
  ridsub* []       = refl
  ridsub* (t ∷ ts) = _∷_ & ridsub t ⊗ ridsub* ts

  eqwksub : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            (sub (lift* {A = B} ss) ∘ wk) t ≡ (wk ∘ sub ss) t
  eqwksub ss t = eqsubren (lift* ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & (eqrenget* (wk⊆ id⊆) id⊆ ss ⋮ (ren* (wk⊆ id⊆)) & lidget* ss)
               ⋮ eqrensub (wk⊆ id⊆) ss t

  eqwksub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  --         (sub* (lift* {A = B} ss) ∘ wk*) ts ≡ (wk* ∘ sub* ss) ts
             (wk* ts) ● (lift* {A = B} ss) ≡ wk* (ts ● ss)
  eqwksub* ss []       = refl
  eqwksub* ss (t ∷ ts) = _∷_ & eqwksub ss t ⊗ eqwksub* ss ts

  eqliftsub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  --           (sub* (lift* {A = B} ss) ∘ lift*) ts ≡ (lift* ∘ sub* ss) ts
               (lift* ts) ● (lift* {A = B} ss) ≡ lift* (ts ● ss)
  eqliftsub* ss ts = (_∷ (sub* (lift* ss) ∘ wk*) ts) & lidsub (lift* ss) zero
                   ⋮ (var zero ∷_) & eqwksub* ss ts


----------------------------------------------------------------------------------------------------

record RenSubKit3Params : Set₁ where
  constructor kit
  field
    rensubkit2 : RenSubKit2Params
  open RenSubKit2Params rensubkit2 public
  open RenSubKit2 rensubkit2 public hiding (rensubkit2)
  field
    compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
--            sub (sub* ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
              sub (ss ● ss′) t ≡ (sub ss ⨾ sub ss′) t

module RenSubKit3 (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  rensubkit3 = ¶

  eqsub : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          (sub (s ∷ ss) ∘ wk) t ≡ sub ss t
  eqsub s ss t = eqsubren (s ∷ ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & lidget* ss

  eqsub* : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  --       (sub* (s ∷ ss) ∘ wk*) ts ≡ sub* ss ts
           (wk* ts) ● (s ∷ ss) ≡ ts ● ss
  eqsub* s ss []       = refl
  eqsub* s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsub* s ss ts

  -- Kovacs: idlₛ
  lidsub* : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) →
  --        sub* ss id* ≡ ss
            id* ● ss ≡ ss
  lidsub* []       = refl
  lidsub* (s ∷ ss) = (_∷ (sub* (s ∷ ss) ∘ wk*) id*) & lidsub (s ∷ ss) zero
                   ⋮ (s ∷_) & (eqsub* s ss id* ⋮ lidsub* ss)

  -- Kovacs: assₛ
  asssub* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  --        sub* (sub* ss′ ss) ts ≡ (sub* ss′ ∘ sub* ss) ts
            ts ● (ss ● ss′) ≡ (ts ● ss) ● ss′
  asssub* ss′ ss []       = refl
  asssub* ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ asssub* ss′ ss ts

  ⟪sub*⟫ : Category lzero lzero
  ⟪sub*⟫ = record
             { Obj  = Ctx
             ; _▻_  = _⊢*_
             ; id   = id*
             ; _∘_  = _●_ -- flip sub*
             ; lid▻ = lidsub*
             ; rid▻ = ridsub*
             ; ass▻ = λ ss′ ss ts → asssub* ts ss ss′
             }

  module _ (⚠ : FunExt) where
    ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪sub*⟫ lzero
    ⟪sub⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub
                ; idƒ  = ⚠ ridsub
                ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                }

  rencut : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           ren (lift⊆ e) t₁ [ ren e t₂ ] ≡ ren e (t₁ [ t₂ ])
  rencut e t₁ t₂ =
      begin
        ren (lift⊆ e) t₁ [ ren e t₂ ]
      ≡⟨⟩
        (sub (ren e t₂ ∷ id*) ∘ ren (lift⊆ e)) t₁
      ≡˘⟨ eqsubren (ren e t₂ ∷ id*) (lift⊆ e) t₁ ⟩
        sub (get* (lift⊆ e) (ren e t₂ ∷ id*)) t₁
      ≡⟨ (flip sub t₁ ∘ (ren e t₂ ∷_)) & (
          begin
            get* e id*
          ≡⟨ ridget* e ⟩
            var* e
          ≡˘⟨ lidren* e ⟩
            ren* e id*
          ∎) ⟩
        sub (ren e t₂ ∷ ren* e id*) t₁
      ≡⟨ eqrensub e (t₂ ∷ id*) t₁ ⟩
        (ren e ∘ sub (t₂ ∷ id*)) t₁
      ≡⟨⟩
        ren e (t₁ [ t₂ ])
      ∎

  subcut : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           sub (lift* ss) t₁ [ sub ss t₂ ] ≡ sub ss (t₁ [ t₂ ])
  subcut ss t₁ t₂ =
      begin
        sub (lift* ss) t₁ [ sub ss t₂ ]
      ≡⟨⟩
        (sub (sub ss t₂ ∷ id*) ∘ sub (lift* ss)) t₁
      ≡˘⟨ compsub (sub ss t₂ ∷ id*) (lift* ss) t₁ ⟩
        sub (sub* (sub ss t₂ ∷ id*) (lift* ss)) t₁
      ≡⟨ (flip sub t₁ ∘ (_∷ (sub* (sub ss t₂ ∷ id*) ∘ wk*) ss)) & lidsub (sub ss t₂ ∷ id*) zero ⟩
        sub (sub ss t₂ ∷ sub* (sub ss t₂ ∷ id*) (wk* ss)) t₁
      ≡⟨ (flip sub t₁ ∘ (sub ss t₂ ∷_)) & (
          begin
            (sub* (sub ss t₂ ∷ id*) ∘ wk*) ss
          ≡˘⟨ eqsubren* (sub ss t₂ ∷ id*) (wk⊆ id⊆) ss ⟩
            sub* (get* (wk⊆ id⊆) (sub ss t₂ ∷ id*)) ss
          ≡⟨⟩
            sub* (get* id⊆ id*) ss
          ≡⟨ flip sub* ss & lidget* id* ⟩
            sub* id* ss
          ≡⟨ ridsub* ss ⟩
            ss
          ≡˘⟨ lidsub* ss ⟩
            sub* ss id*
          ∎) ⟩
        sub (sub* ss (t₂ ∷ id*)) t₁
      ≡⟨ compsub ss (t₂ ∷ id*) t₁ ⟩
        (sub ss ∘ sub (t₂ ∷ id*)) t₁
      ≡⟨⟩
        sub ss (t₁ [ t₂ ])
      ∎


----------------------------------------------------------------------------------------------------
