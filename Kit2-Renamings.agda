module Kit2-Renamings where

open import Kit1-Renamings public
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
    compren : ∀ {Γ Γ′ Γ″ A} (js′ : Γ′ ⊆ Γ″) (js : Γ ⊆ Γ′) (t : Γ ⊢ A) →
              ren (js′ ∘⊆ js) t ≡ (ren js′ ∘ ren js) t
    --        ren (js ○ js′) t ≡ (ren js′ ∘ ren js) t
    ridren  : ∀ {Γ Γ′ A} (js : Γ ⊆ Γ′) (i : Γ ∋ A) → ren js (var i) ≡ var (ren∋ js i)
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
  compren* : ∀ {Γ Γ′ Γ″ Δ} (js′ : Γ′ ⊆ Γ″) (js : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             ren* (js′ ∘⊆ js) ts ≡ (ren* js′ ∘ ren* js) ts
  --         ts ◐ (js ○ js′) ≡ (ts ◐ js) ◐ js′
  compren* js′ js []       = refl
  compren* js′ js (t ∷ ts) = _∷_ & compren js′ js t ⊗ compren* js′ js ts

  eqren : ∀ {Γ Γ′ A B} (j : Γ′ ∋ B) (js : Γ ⊆ Γ′) (t : Γ ⊢ A) →
          (ren (j ∷ js) ∘ wk) t ≡ ren js t
  eqren j js t = compren (j ∷ js) (wk⊆ id⊆) t ⁻¹
               ⋮ flip ren t & (eq⊆ j js id⊆ ⋮ rid⊆ js)

  eqwkren : ∀ {Γ Γ′ A B} (js : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            (ren (lift⊆ js) ∘ wk) t ≡ (wk {B = B} ∘ ren js) t
  eqwkren js t = eqren zero (wk⊆ js) t
               ⋮ flip ren t & eqwk⊆′ js ⁻¹
               ⋮ compren (wk⊆ id⊆) js t

  eqren* : ∀ {Γ Γ′ Δ B} (j : Γ′ ∋ B) (js : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
           (ren* (j ∷ js) ∘ wk*) ts ≡ ren* js ts
  --       (wk* ts) ◐ (j ∷ js) ≡ ts ◐ js
  eqren* j js []       = refl
  eqren* j js (t ∷ ts) = _∷_ & eqren j js t ⊗ eqren* j js ts

  eqwkren* : ∀ {Γ Γ′ Δ B} (js : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             (ren* (lift⊆ js) ∘ wk*) ts ≡ (wk* {B = B} ∘ ren* js) ts
  --         (wk* ts) ◐ (lift⊆ js) ≡ wk* {B = B} (ts ◐ js)
  eqwkren* js []       = refl
  eqwkren* js (t ∷ ts) = _∷_ & eqwkren js t ⊗ eqwkren* js ts

  eqliftren* : ∀ {Γ Γ′ Δ B} (js : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
               (ren* (lift⊆ js) ∘ lift*) ts ≡ (lift* {B = B} ∘ ren* js) ts
  --           (lift* ts) ◐ (lift⊆ js) ≡ lift* {B = B} (ts ◐ js)
  eqliftren* js ts = (_∷ (ren* (lift⊆ js) ∘ wk*) ts) & ridren (lift⊆ js) zero
                   ⋮ (var zero ∷_) & eqwkren* js ts

  -- Kovacs: idlₛₑ; not really identity
  ridren* : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) →
            ren* is id* ≡ var* is
  --        id* ◐ is ≡ var* is
  ridren* []       = refl
  ridren* (i ∷ is) = _∷_ & ridren (i ∷ is) zero
                         ⊗ (eqren* i is id* ⋮ ridren* is)

  module _ (⚠ : FunExt) where
    ⟪ren⟫ : ∀ (A : Ty) → Presheaf ⟪⊇⟫ lzero
    ⟪ren⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = ren
                ; idƒ  = ⚠ lidren
                ; _∘ƒ_ = λ js′ js → ⚠ (compren js′ js)
                }

    ⟪ren*⟫ : ∀ (Δ : Ctx) → Presheaf ⟪⊇⟫ lzero
    ⟪ren*⟫ Δ = record
                 { ƒObj = _⊢* Δ
                 ; ƒ    = ren* -- flip _◐_
                 ; idƒ  = ⚠ lidren*
                 ; _∘ƒ_ = λ js′ js → ⚠ (compren* js′ js)
                 }

  -- Kovacs: ∈-ₛ∘ₑa
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (js : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
              sub∋ (ren* js ss) i ≡ (ren js ∘ sub∋ ss) i
  --          sub∋ (ss ◐ js) i ≡ (sub∋ ss ⨾ ren js) i
  eqrensub∋ js (s ∷ ss) zero    = refl
  eqrensub∋ js (s ∷ ss) (suc i) = eqrensub∋ js ss i

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
              sub∋ (get* js ss) i ≡ (sub∋ ss ∘ ren∋ js) i
  --          sub∋ (js ◑ ss) i ≡ (ren∋ js ⨾ sub∋ ss) i
  eqsubren∋ ss (j ∷ js) zero    = ridsub ss j
  eqsubren∋ ss (j ∷ js) (suc i) = eqsubren∋ ss js i

  -- Kovacs: ∈-idₛ; not really identity
  idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ id* i ≡ var i
  idsub∋ zero    = refl
  idsub∋ (suc i) = eqrensub∋ (wk⊆ id⊆) id* i
                 ⋮ wk & idsub∋ i
                 ⋮ ridren (wk⊆ id⊆) i
                 ⋮ var & (eqwkren∋ id⊆ i ⋮ suc & idren∋ i)

  -- Kovacs: ∈-∘ₛ; not really composition
  compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
             sub∋ (sub* ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
  --         sub∋ (ss ● ss′) i ≡ (sub∋ ss ⨾ sub ss′) i
  compsub∋ ss′ (s ∷ ss) zero    = refl
  compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i

  eqget* : ∀ {Γ Γ′ Ξ A} (is : Γ ⊆ Γ′) (s : Ξ ⊢ A) (ss : Ξ ⊢* Γ′) →
           get* (wk⊆ is) (s ∷ ss) ≡ get* is ss
  --       (wk⊆ is) ◑ (s ∷ ss) ≡ is ◑ ss
  eqget* []       s ss = refl
  eqget* (i ∷ is) s ss = _∷_ & (ridsub (s ∷ ss) (suc i) ⋮ ridsub ss i ⁻¹)
                             ⊗ eqget* is s ss

  -- Kovacs: idlₑₛ
  lidget* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
            get* id⊆ ts ≡ ts
  --        id⊆ ◑ ts ≡ ts
  lidget* []       = refl
  lidget* (t ∷ ts) = _∷_ & ridsub (t ∷ ts) zero
                         ⊗ (eqget* id⊆ t ts ⋮ lidget* ts)

  compget* : ∀ {Γ Δ Δ′ Δ″} (js : Δ ⊆ Δ′) (js′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
             get* (js′ ∘⊆ js) ts ≡ (get* js ∘ get* js′) ts
  --         (js ○ js′) ◑ ts ≡ js ◑ (js′ ◑ ts)
  compget* []       js′ ts = refl
  compget* (j ∷ js) js′ ts = _∷_ & ( ridsub ts (ren∋ js′ j)
                                   ⋮ eqsubren∋ ts js′ j ⁻¹
                                   ⋮ ridsub (get* js′ ts) j ⁻¹
                                   )
                                 ⊗ compget* js js′ ts

  module _ (⚠ : FunExt) where
    ⟪get*⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ lzero
    ⟪get*⟫ Γ = record
                 { ƒObj = Γ ⊢*_
                 ; ƒ    = get* -- _◑_
                 ; idƒ  = ⚠ lidget*
                 ; _∘ƒ_ = λ e e′ → ⚠ (compget* e e′)
                 }


----------------------------------------------------------------------------------------------------

record RenSubKit2Params : Set₁ where
  constructor kit
  field
    rensubkit1 : RenSubKit1Params
  open RenSubKit1Params rensubkit1 public
  open RenSubKit1 rensubkit1 public hiding (rensubkit1)
  field
    eqrensub : ∀ {Γ Ξ Ξ′ A} (js : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
               sub (ren* js ss) t ≡ (ren js ∘ sub ss) t
    --         sub (ss ◐ js) t ≡ (sub ss ⨾ ren js) t

module RenSubKit2 (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  rensubkit2 = ¶

  -- Kovacs: assₛₛₑ
  eqrensub* : ∀ {Γ Ξ Ξ′ Δ} (js : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
              sub* (ren* js ss) ts ≡ (ren* js ∘ sub* ss) ts
  --          ts ● (ss ◐ js) ≡ (ts ● ss) ◐ js
  eqrensub* js ss []       = refl
  eqrensub* js ss (t ∷ ts) = _∷_ & eqrensub js ss t ⊗ eqrensub* js ss ts

  -- Kovacs: assₑₛₑ
  eqrenget* : ∀ {Γ Γ′ Δ Δ′} (js : Γ ⊆ Γ′) (js′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
              (get* js′ ∘ ren* js) ts ≡ (ren* js ∘ get* js′) ts
  --          js′ ◑ (ts ◐ js) ≡ (js′ ◑ ts) ◐ js
  eqrenget* js []         ts = refl
  eqrenget* js (j′ ∷ js′) ts = _∷_ & eqrensub js ts (var j′) ⊗ eqrenget* js js′ ts

  eqwkget* : ∀ {Γ Δ Δ′ B} (js : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
             (get* (wk⊆ js) ∘ lift*) ts ≡ (wk* {B = B} ∘ get* js) ts
  --         (wk⊆ js) ◑ (lift* ts) ≡ wk* {B = B} (js ◑ ts)
  eqwkget* js ts = eqget* js (var zero) (wk* ts) ⋮ eqrenget* (wk⊆ id⊆) js ts

  eqliftget* : ∀ {Γ Δ Δ′ B} (js : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
               (get* (lift⊆ js) ∘ lift*) ts ≡ (lift* {B = B} ∘ get* js) ts
  --           (lift⊆ js) ◑ (lift* ts) ≡ lift* {B = B} (js ◑ ts)
  eqliftget* js ts = _∷_ & ridsub (lift* ts) zero ⊗ eqwkget* js ts

  -- Kovacs: idrₑₛ; not really identity
  ridget* : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) →
            get* is id* ≡ var* is
  --        is ◑ id* ≡ var* is
  ridget* []       = refl
  ridget* (i ∷ is) = _∷_ & (ridsub id* i ⋮ idsub∋ i)
                         ⊗ ridget* is


----------------------------------------------------------------------------------------------------

record RenSubKit3Params : Set₁ where
  constructor kit
  field
    rensubkit2 : RenSubKit2Params
  open RenSubKit2Params rensubkit2 public
  open RenSubKit2 rensubkit2 public hiding (rensubkit2)
  field
    eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (js : Γ ⊆ Γ′) (t : Γ ⊢ A) →
               sub (get* js ss) t ≡ (sub ss ∘ ren js) t
    --         sub (js ◑ ss) t ≡ (ren js ⨾ sub ss) t
    lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub id* t ≡ t

module RenSubKit3 (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  rensubkit3 = ¶

  -- Kovacs: assₛₑₛ
  eqsubren* : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (js : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
              sub* (get* js ss) ts ≡ (sub* ss ∘ ren* js) ts
  --          ts ● (js ◑ ss) ≡ (ts ◐ js) ● ss
  eqsubren* ss js []       = refl
  eqsubren* ss js (t ∷ ts) = _∷_ & eqsubren ss js t ⊗ eqsubren* ss js ts

  -- Kovacs: idrₛ
  lidsub* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → sub* id* ts ≡ ts
  lidsub* []       = refl
  lidsub* (t ∷ ts) = _∷_ & lidsub t ⊗ lidsub* ts

  eqsub : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          (sub (s ∷ ss) ∘ wk) t ≡ sub ss t
  eqsub s ss t = eqsubren (s ∷ ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & (eqget* id⊆ s ss ⋮ lidget* ss)

  eqsub* : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
           (sub* (s ∷ ss) ∘ wk*) ts ≡ sub* ss ts
  --       (wk* ts) ● (s ∷ ss) ≡ ts ● ss
  eqsub* s ss []       = refl
  eqsub* s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsub* s ss ts

  eqwksub : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            (sub (lift* ss) ∘ wk) t ≡ (wk {B = B} ∘ sub ss) t
  eqwksub ss t = eqsubren (lift* ss) (wk⊆ id⊆) t ⁻¹
               ⋮ flip sub t & (eqwkget* id⊆ ss ⋮ wk* & lidget* ss)
               ⋮ eqrensub (wk⊆ id⊆) ss t

  eqwksub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             (sub* (lift* ss) ∘ wk*) ts ≡ (wk* {B = B} ∘ sub* ss) ts
  --         (wk* ts) ● (lift* ss) ≡ wk* {B = B} (ts ● ss)
  eqwksub* ss []       = refl
  eqwksub* ss (t ∷ ts) = _∷_ & eqwksub ss t ⊗ eqwksub* ss ts

  eqliftsub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
               (sub* (lift* ss) ∘ lift*) ts ≡ (lift* {B = B} ∘ sub* ss) ts
  --           (lift* ts) ● (lift* ss) ≡ lift* {B = B} (ts ● ss)
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

record RenSubKit4Params : Set₁ where
  constructor kit
  field
    rensubkit3 : RenSubKit3Params
  open RenSubKit3Params rensubkit3 public
  open RenSubKit3 rensubkit3 public hiding (rensubkit3)
  field
    compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
              sub (sub* ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
    --        sub (ss ● ss′) t ≡ (sub ss ⨾ sub ss′) t

module RenSubKit4 (¶ : RenSubKit4Params) where
  open RenSubKit4Params ¶
  rensubkit4 = ¶

  -- Kovacs: assₛ
  asssub* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
            (sub* ss′ ∘ sub* ss) ts ≡ sub* (sub* ss′ ss) ts
  --        (ts ● ss) ● ss′ ≡ ts ● (ss ● ss′)
  asssub* ss′ ss []       = refl
  asssub* ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⁻¹ ⊗ asssub* ss′ ss ts

  ⟪*⊣⟫ : Category lzero lzero
  ⟪*⊣⟫ = record
            { Obj  = Ctx
            ; _▻_  = flip _⊢*_
            ; id   = id*
            ; _∘_  = sub* -- flip _●_
            ; lid▻ = lidsub*
            ; rid▻ = ridsub*
            ; ass▻ = asssub*
            }

  ⟪⊢*⟫ : Category lzero lzero
  ⟪⊢*⟫ = ⟪*⊣⟫ ᵒᵖ

  module _ (⚠ : FunExt) where
    ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪⊢*⟫ lzero
    ⟪sub⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub
                ; idƒ  = ⚠ lidsub
                ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                }

  rencut : ∀ {Γ Γ′ A B} (js : Γ ⊆ Γ′) (t₁ : (A ∷ Γ) ⊢ B) (t₂ : Γ ⊢ A) →
           ren (lift⊆ js) t₁ [ ren js t₂ ] ≡ ren js (t₁ [ t₂ ])
  rencut js t₁ t₂ =
      begin
        ren (lift⊆ js) t₁ [ ren js t₂ ]
      ≡⟨⟩
        (sub (ren js t₂ ∷ id*) ∘ ren (lift⊆ js)) t₁
      ≡⟨ eqsubren (ren js t₂ ∷ id*) (lift⊆ js) t₁ ⁻¹ ⟩
        sub (get* (lift⊆ js) (ren js t₂ ∷ id*)) t₁
      ≡⟨ flip sub t₁ & (
          begin
            get* (lift⊆ js) (ren js t₂ ∷ id*)
          ≡⟨⟩
            sub (ren js t₂ ∷ id*) (var zero) ∷ get* (wk⊆ js) (ren js t₂ ∷ id*)
          ≡⟨ _∷_ & ridsub (ren js t₂ ∷ id*) zero ⊗ eqget* js (ren js t₂) id* ⟩
            ren js t₂ ∷ get* js id*
          ≡⟨ (ren js t₂ ∷_) & (ridget* js ⋮ ridren* js ⁻¹) ⟩
            ren js t₂ ∷ ren* js id*
          ∎) ⟩
        sub (ren js t₂ ∷ ren* js id*) t₁
      ≡⟨ eqrensub js (t₂ ∷ id*) t₁ ⟩
        (ren js ∘ sub (t₂ ∷ id*)) t₁
      ≡⟨⟩
        ren js (t₁ [ t₂ ])
      ∎

  subcut : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : (A ∷ Γ) ⊢ B) (t₂ : Γ ⊢ A) →
           sub (lift* ss) t₁ [ sub ss t₂ ] ≡ sub ss (t₁ [ t₂ ])
  subcut ss t₁ t₂ =
      begin
        sub (lift* ss) t₁ [ sub ss t₂ ]
      ≡⟨⟩
        (sub (sub ss t₂ ∷ id*) ∘ sub (lift* ss)) t₁
      ≡⟨ compsub (sub ss t₂ ∷ id*) (lift* ss) t₁ ⁻¹ ⟩
        sub (sub* (sub ss t₂ ∷ id*) (lift* ss)) t₁
      ≡⟨ (flip sub t₁ ∘ (_∷ (sub* (sub ss t₂ ∷ id*) ∘ wk*) ss)) & ridsub (sub ss t₂ ∷ id*) zero ⟩
        sub (sub ss t₂ ∷ sub* (sub ss t₂ ∷ id*) (wk* ss)) t₁
      ≡⟨ (flip sub t₁ ∘ (sub ss t₂ ∷_)) & (
          begin
            (sub* (sub ss t₂ ∷ id*) ∘ wk*) ss
          ≡⟨ eqsubren* (sub ss t₂ ∷ id*) (wk⊆ id⊆) ss ⁻¹ ⟩
            sub* (get* (wk⊆ id⊆) (sub ss t₂ ∷ id*)) ss
          ≡⟨ flip sub* ss & (eqget* id⊆ (sub ss t₂) id* ⋮ lidget* id*) ⟩
            sub* id* ss
          ≡⟨ lidsub* ss ⋮ ridsub* ss ⁻¹ ⟩
            sub* ss id*
          ∎) ⟩
        sub (sub* ss (t₂ ∷ id*)) t₁
      ≡⟨ compsub ss (t₂ ∷ id*) t₁ ⟩
        (sub ss ∘ sub (t₂ ∷ id*)) t₁
      ≡⟨⟩
        sub ss (t₁ [ t₂ ])
      ∎


----------------------------------------------------------------------------------------------------
