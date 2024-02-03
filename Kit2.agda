module Kit2 where

open import Kit1 public


----------------------------------------------------------------------------------------------------

record RenSubKit1Params : Set₁ where
  constructor kit
  field
    subkit : SubKitParams
  open SubKitParams subkit public
  open SubKit subkit public hiding (subkit)
  field
    lidren  : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
    ridren  : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
    compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
                ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t

module RenSubKit1 (κ : RenSubKit1Params) where
  open RenSubKit1Params κ
  rensubkit1 = κ

  lidrens : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → rens id⊆ ts ≡ ts
  lidrens []       = refl
  lidrens (t ∷ ts) = _∷_ & lidren t ⊗ lidrens ts

  -- Kovacs: assₛₑₑ
  comprens : ∀ {Γ Γ′ Γ″ Δ} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             rens (e′ ∘⊆ e) ts ≡ (rens e′ ∘ rens e) ts
  comprens e′ e []       = refl
  comprens e′ e (t ∷ ts) = _∷_ & compren e′ e t ⊗ comprens e′ e ts

  eqwkren : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            (ren (keep {A = B} e) ∘ wk) t ≡ (wk ∘ ren e) t
  eqwkren e t = compren (keep e) wk⊆ t ⁻¹
              ⋮ (flip ren t ∘ drop) & (rid⊆ e ⋮ lid⊆ e ⁻¹)
              ⋮ compren wk⊆ e t

  eqwkrens : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             (rens (keep {A = B} e) ∘ wks) ts ≡ (wks ∘ rens e) ts
  eqwkrens e []       = refl
  eqwkrens e (t ∷ ts) = _∷_ & eqwkren e t ⊗ eqwkrens e ts

  eqliftrens : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
               (rens (keep {A = B} e) ∘ lifts) ts ≡ (lifts ∘ rens e) ts
  eqliftrens e ts = (_∷ (rens (keep e) ∘ wks) ts) & ridren (keep e) zero
                  ⋮ (var zero ∷_) & eqwkrens e ts

  -- Kovacs: idlₛₑ; not really identity
  ridrens : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → rens e ids ≡ vars e
  ridrens stop     = refl
  ridrens (drop e) = (flip rens ids ∘ drop) & lid⊆ e ⁻¹
                   ⋮ comprens wk⊆ e ids
                   ⋮ wks & ridrens e
  ridrens (keep e) = (_∷ (rens (keep e) ∘ wks) ids) & ridren (keep e) zero
                   ⋮ (var zero ∷_) & (eqwkrens e ids ⋮ wks & ridrens e)

  module _ (⚠ : Funext) where
    ⟪ren⟫ : ∀ (A : Ty) → Presheaf (⟪⊆⟫ ᵒᵖ) lzero
    ⟪ren⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = ren
                ; idƒ  = ⚠ lidren
                ; _∘ƒ_ = λ e′ e → ⚠ (compren e′ e)
                }

    ⟪rens⟫ : ∀ (Δ : Ctx) → Presheaf (⟪⊆⟫ ᵒᵖ) lzero
    ⟪rens⟫ Δ = record
                 { ƒObj = _⊢* Δ
                 ; ƒ    = rens
                 ; idƒ  = ⚠ lidrens
                 ; _∘ƒ_ = λ e′ e → ⚠ (comprens e′ e)
                 }

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
              sub∋ (gets e ss) i ≡ (sub∋ ss ∘ ren∋ e) i
  eqsubren∋ []       stop     i       = refl
  eqsubren∋ (s ∷ ss) (drop e) i       = eqsubren∋ ss e i
  eqsubren∋ (s ∷ ss) (keep e) zero    = refl
  eqsubren∋ (s ∷ ss) (keep e) (suc i) = eqsubren∋ ss e i

  -- Kovacs: idlₑₛ
  lidgets : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → gets id⊆ ts ≡ ts
  lidgets []       = refl
  lidgets (t ∷ ts) = (t ∷_) & lidgets ts

  compgets : ∀ {Γ Δ Δ′ Δ″} (e : Δ ⊆ Δ′) (e′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
             gets (e′ ∘⊆ e) ts ≡ (gets e ∘ gets e′) ts
  compgets e        stop      []       = refl
  compgets e        (drop e′) (t ∷ ts) = compgets e e′ ts
  compgets (drop e) (keep e′) (t ∷ ts) = compgets e e′ ts
  compgets (keep e) (keep e′) (t ∷ ts) = (t ∷_) & compgets e e′ ts

  -- Kovacs: assₑₛₑ
  eqrengets : ∀ {Γ Γ′ Δ Δ′} (e : Γ ⊆ Γ′) (e′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
              (gets e′ ∘ rens e) ts ≡ (rens e ∘ gets e′) ts
  eqrengets e stop      []       = refl
  eqrengets e (drop e′) (t ∷ ts) = eqrengets e e′ ts
  eqrengets e (keep e′) (t ∷ ts) = (ren e t ∷_) & eqrengets e e′ ts

  eqliftgets : ∀ {Γ Δ Δ′ B} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
               (gets (keep {A = B} e) ∘ lifts) ts ≡ (lifts ∘ gets e) ts
  eqliftgets e ts = (var zero ∷_) & eqrengets wk⊆ e ts

  -- Kovacs: idrₑₛ; not really identity
  ridgets : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → gets e ids ≡ vars e
  ridgets stop     = refl
  ridgets (drop e) = eqrengets wk⊆ e ids ⋮ wks & ridgets e
  ridgets (keep e) = (var zero ∷_) & (eqrengets wk⊆ e ids ⋮ wks & ridgets e)

  module _ (⚠ : Funext) where
    ⟪gets⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ lzero
    ⟪gets⟫ Γ = record
                 { ƒObj = Γ ⊢*_
                 ; ƒ    = gets
                 ; idƒ  = ⚠ lidgets
                 ; _∘ƒ_ = λ e e′ → ⚠ (compgets e e′)
                 }

  -- Kovacs: ∈-ₛ∘ₑa
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
              sub∋ (rens e ss) i ≡ (ren e ∘ sub∋ ss) i
  eqrensub∋ e (s ∷ ss) zero    = refl
  eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

  -- Kovacs: ∈-idₛ; not really identity
  idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ ids i ≡ var i
  idsub∋ zero    = refl
  idsub∋ (suc i) = eqrensub∋ wk⊆ ids i
                 ⋮ wk & idsub∋ i
                 ⋮ ridren wk⊆ i
                 ⋮ (var ∘ suc) & idren∋ i

  -- Kovacs: ∈-∘ₛ; not really composition
  compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
             sub∋ (subs ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
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
               sub (gets e ss) t ≡ (sub ss ∘ ren e) t
    eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
               sub (rens e ss) t ≡ (ren e ∘ sub ss) t
    lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub ids t ≡ t
    ridsub   : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i

module RenSubKit2 (κ : RenSubKit2Params) where
  open RenSubKit2Params κ
  rensubkit2 = κ

  -- Kovacs: assₛₑₛ
  eqsubrens : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
              subs (gets e ss) ts ≡ (subs ss ∘ rens e) ts
  eqsubrens ss e []       = refl
  eqsubrens ss e (t ∷ ts) = _∷_ & eqsubren ss e t ⊗ eqsubrens ss e ts

  -- Kovacs: assₛₛₑ
  eqrensubs : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
              subs (rens e ss) ts ≡ (rens e ∘ subs ss) ts
  eqrensubs e ss []       = refl
  eqrensubs e ss (t ∷ ts) = _∷_ & eqrensub e ss t ⊗ eqrensubs e ss ts

  -- Kovacs: idrₛ
  lidsubs : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → subs ids ts ≡ ts
  lidsubs []       = refl
  lidsubs (t ∷ ts) = _∷_ & lidsub t ⊗ lidsubs ts

  eqwksub : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            (sub (lifts {A = B} ss) ∘ wk) t ≡ (wk ∘ sub ss) t
  eqwksub ss t = eqsubren (lifts ss) wk⊆ t ⁻¹
               ⋮ flip sub t & (eqrengets wk⊆ id⊆ ss ⋮ (rens wk⊆) & lidgets ss)
               ⋮ eqrensub wk⊆ ss t

  eqwksubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             (subs (lifts {A = B} ss) ∘ wks) ts ≡ (wks ∘ subs ss) ts
  eqwksubs ss []       = refl
  eqwksubs ss (t ∷ ts) = _∷_ & eqwksub ss t ⊗ eqwksubs ss ts

  eqliftsubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
               (subs (lifts {A = B} ss) ∘ lifts) ts ≡ (lifts ∘ subs ss) ts
  eqliftsubs ss ts = (_∷ (subs (lifts ss) ∘ wks) ts) & ridsub (lifts ss) zero
                   ⋮ (var zero ∷_) & eqwksubs ss ts


----------------------------------------------------------------------------------------------------

record RenSubKit3Params : Set₁ where
  constructor kit
  field
    rensubkit2 : RenSubKit2Params
  open RenSubKit2Params rensubkit2 public
  open RenSubKit2 rensubkit2 public hiding (rensubkit2)
  field
    compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
              sub (subs ss′ ss) t ≡ (sub ss′ ∘ sub ss) t

module RenSubKit3 (κ : RenSubKit3Params) where
  open RenSubKit3Params κ
  rensubkit3 = κ

  compsubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
  compsubs ss′ ss []       = refl
  compsubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ compsubs ss′ ss ts

  eqsub : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          (sub (s ∷ ss) ∘ wk) t ≡ sub ss t
  eqsub s ss t = eqsubren (s ∷ ss) (drop id⊆) t ⁻¹
               ⋮ flip sub t & lidgets ss

  eqsubs : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
           (subs (s ∷ ss) ∘ wks) ts ≡ subs ss ts
  eqsubs s ss []       = refl
  eqsubs s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsubs s ss ts

  -- Kovacs: idlₛ
  ridsubs : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) → subs ss ids ≡ ss
  ridsubs []       = refl
  ridsubs (s ∷ ss) = (_∷ (subs (s ∷ ss) ∘ wks) ids) & ridsub (s ∷ ss) zero
                   ⋮ (s ∷_) & (eqsubs s ss ids ⋮ ridsubs ss)

  -- Kovacs: assₛ
  asssubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
            subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
  asssubs ss′ ss []       = refl
  asssubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ asssubs ss′ ss ts

  ⟪subs⟫ : Category lzero lzero
  ⟪subs⟫ = record
             { Obj  = Ctx
             ; _▻_  = _⊢*_
             ; id   = ids
             ; _∘_  = flip subs
             ; lid▻ = ridsubs
             ; rid▻ = lidsubs
             ; ass▻ = λ ss′ ss ts → asssubs ts ss ss′
             }

  module _ (⚠ : Funext) where
    ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪subs⟫ lzero
    ⟪sub⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub
                ; idƒ  = ⚠ lidsub
                ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                }

  module _ where
    open ≡-Reasoning

    rencut : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t₁ : (A ∷ Γ) ⊢ B) (t₂ : Γ ⊢ A) →
             ren (keep e) t₁ [ ren e t₂ ] ≡ ren e (t₁ [ t₂ ])
    rencut e t₁ t₂ =
        begin
          ren (keep e) t₁ [ ren e t₂ ]
        ≡⟨⟩
          (sub (ren e t₂ ∷ ids) ∘ ren (keep e)) t₁
        ≡˘⟨ eqsubren (ren e t₂ ∷ ids) (keep e) t₁ ⟩
          sub (gets (keep e) (ren e t₂ ∷ ids)) t₁
        ≡⟨ (flip sub t₁ ∘ (ren e t₂ ∷_)) & (
            begin
              gets e ids
            ≡⟨ ridgets e ⟩
              vars e
            ≡˘⟨ ridrens e ⟩
              rens e ids
            ∎) ⟩
          sub (ren e t₂ ∷ rens e ids) t₁
        ≡⟨ eqrensub e (t₂ ∷ ids) t₁ ⟩
          (ren e ∘ sub (t₂ ∷ ids)) t₁
        ≡⟨⟩
          ren e (t₁ [ t₂ ])
        ∎

    subcut : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : (A ∷ Γ) ⊢ B) (t₂ : Γ ⊢ A) →
             sub (lifts ss) t₁ [ sub ss t₂ ] ≡ sub ss (t₁ [ t₂ ])
    subcut ss t₁ t₂ =
        begin
          sub (lifts ss) t₁ [ sub ss t₂ ]
        ≡⟨⟩
          (sub (sub ss t₂ ∷ ids) ∘ sub (lifts ss)) t₁
        ≡˘⟨ compsub (sub ss t₂ ∷ ids) (lifts ss) t₁ ⟩
          sub (subs (sub ss t₂ ∷ ids) (lifts ss)) t₁
        ≡⟨ (flip sub t₁ ∘ (_∷ (subs (sub ss t₂ ∷ ids) ∘ wks) ss)) & ridsub (sub ss t₂ ∷ ids) zero ⟩
          sub (sub ss t₂ ∷ subs (sub ss t₂ ∷ ids) (wks ss)) t₁
        ≡⟨ (flip sub t₁ ∘ (sub ss t₂ ∷_)) & (
            begin
              (subs (sub ss t₂ ∷ ids) ∘ wks) ss
            ≡˘⟨ eqsubrens (sub ss t₂ ∷ ids) (drop id⊆) ss ⟩
              subs (gets (drop id⊆) (sub ss t₂ ∷ ids)) ss
            ≡⟨⟩
              subs (gets id⊆ ids) ss
            ≡⟨ flip subs ss & lidgets ids ⟩
              subs ids ss
            ≡⟨ lidsubs ss ⟩
              ss
            ≡˘⟨ ridsubs ss ⟩
              subs ss ids
            ∎) ⟩
          sub (subs ss (t₂ ∷ ids)) t₁
        ≡⟨ compsub ss (t₂ ∷ ids) t₁ ⟩
          (sub ss ∘ sub (t₂ ∷ ids)) t₁
        ≡⟨⟩
          sub ss (t₁ [ t₂ ])
        ∎


----------------------------------------------------------------------------------------------------
