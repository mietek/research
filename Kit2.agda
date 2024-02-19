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
    lidren  : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊑ t ≡ t
    compren : ∀ {Γ Γ′ Γ″ A} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
              ren (ϱ′ ∘⊑ ϱ) t ≡ (ren ϱ′ ∘ ren ϱ) t
    --        ren (ϱ ○ ϱ′) t ≡ (ren ϱ′ ∘ ren ϱ) t
    ridren  : ∀ {Γ Γ′ A} (ϱ : Γ ⊑ Γ′) (i : Γ ∋ A) → ren ϱ (var i) ≡ var (ren∋ ϱ i)
    ridsub  : ∀ {Γ Ξ A} (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) → sub σ (var i) ≡ sub∋ σ i

module RenSubKit1 (¶ : RenSubKit1Params) where
  open RenSubKit1Params ¶
  rensubkit1 = ¶

  lidren§ : ∀ {Γ Δ} (τ : Γ ⊢§ Δ) →
            ren§ id⊑ τ ≡ τ
  --        ts ◐ id⊑ ≡ τ
  lidren§ ∙       = refl
  lidren§ (τ , t) = _,_ & lidren§ τ ⊗ lidren t

  -- Kovacs: assₛₑₑ
  compren§ : ∀ {Γ Γ′ Γ″ Δ} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
             ren§ (ϱ′ ∘⊑ ϱ) τ ≡ (ren§ ϱ′ ∘ ren§ ϱ) τ
  --         τ ◐ (ϱ ○ ϱ′) ≡ (τ ◐ ϱ) ◐ ϱ′
  compren§ ϱ′ ϱ ∙       = refl
  compren§ ϱ′ ϱ (τ , t) = _,_ & compren§ ϱ′ ϱ τ ⊗ compren ϱ′ ϱ t

  eqwkren : ∀ {B Γ Γ′ A} (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
            (ren (lift⊑ ϱ) ∘ wk) t ≡ (wk {B} ∘ ren ϱ) t
  eqwkren ϱ t = compren (lift⊑ ϱ) (wk⊑ id⊑) t ⁻¹
              ⋮ (flip ren t ∘ wk⊑) & (rid⊑ ϱ ⋮ lid⊑ ϱ ⁻¹)
              ⋮ compren (wk⊑ id⊑) ϱ t

  eqwkren§ : ∀ {B Γ Γ′ Δ} (ϱ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
             (ren§ (lift⊑ ϱ) ∘ wk§) τ ≡ (wk§ {B} ∘ ren§ ϱ) τ
  --         (wk§ τ) ◐ (lift⊑ ϱ) ≡ wk§ {B} (τ ◐ ϱ)
  eqwkren§ ϱ ∙       = refl
  eqwkren§ ϱ (τ , t) = _,_ & eqwkren§ ϱ τ ⊗ eqwkren ϱ t

  eqliftren§ : ∀ {B Γ Γ′ Δ} (ϱ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
               (ren§ (lift⊑ ϱ) ∘ lift§) τ ≡ (lift§ {B} ∘ ren§ ϱ) τ
  --           (lift§ τ) ◐ (lift⊑ ϱ) ≡ lift§ {B} (τ ◐ ϱ)
  eqliftren§ ϱ τ = ((ren§ (lift⊑ ϱ) ∘ wk§) τ ,_) & ridren (lift⊑ ϱ) zero
                 ⋮ (_, var zero) & eqwkren§ ϱ τ

  -- Kovacs: idlₛₑ; not really identity
  ridren§ : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) →
            ren§ ϱ id§ ≡ var§ ϱ
  --        id§ ◐ ϱ ≡ var§ ϱ
  ridren§ stop      = refl
  ridren§ (wk⊑ ϱ)   = (flip ren§ id§ ∘ wk⊑) & lid⊑ ϱ ⁻¹
                    ⋮ compren§ (wk⊑ id⊑) ϱ id§
                    ⋮ wk§ & ridren§ ϱ
  ridren§ (lift⊑ ϱ) = ((ren§ (lift⊑ ϱ) ∘ wk§) id§ ,_) & ridren (lift⊑ ϱ) zero
                    ⋮ (_, var zero) & (eqwkren§ ϱ id§ ⋮ wk§ & ridren§ ϱ)

  -- Kovacs: ∈-ₛ∘ₑ
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (ϱ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) →
              sub∋ (ren§ ϱ σ) i ≡ (ren ϱ ∘ sub∋ σ) i
  --          sub∋ (σ ◐ ϱ) i ≡ (sub∋ σ ⨾ ren ϱ) i
  eqrensub∋ ϱ (σ , s) zero    = refl
  eqrensub∋ ϱ (σ , s) (wk∋ i) = eqrensub∋ ϱ σ i

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (i : Γ ∋ A) →
              sub∋ (get§ ϱ σ) i ≡ (sub∋ σ ∘ ren∋ ϱ) i
  --          sub∋ (ϱ ◑ σ) i ≡ (ren∋ ϱ ⨾ sub∋ σ) i
  eqsubren∋ ∙       stop      i       = refl
  eqsubren∋ (σ , s) (wk⊑ ϱ)   i       = eqsubren∋ σ ϱ i
  eqsubren∋ (σ , s) (lift⊑ ϱ) zero    = refl
  eqsubren∋ (σ , s) (lift⊑ ϱ) (wk∋ i) = eqsubren∋ σ ϱ i

  -- Kovacs: ∈-idₛ; not really identity
  idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ id§ i ≡ var i
  idsub∋ zero    = refl
  idsub∋ (wk∋ i) = eqrensub∋ (wk⊑ id⊑) id§ i
                 ⋮ wk & idsub∋ i
                 ⋮ ridren (wk⊑ id⊑) i
                 ⋮ (var ∘ wk∋) & idren∋ i

  -- Kovacs: ∈-∘ₛ; not really composition
  compsub∋ : ∀ {Γ Ξ Ξ′ A} (σ′ : Ξ′ ⊢§ Ξ) (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) →
             sub∋ (sub§ σ′ σ) i ≡ (sub σ′ ∘ sub∋ σ) i
  --         sub∋ (σ ● σ′) i ≡ (sub∋ σ ⨾ sub σ′) i
  compsub∋ σ′ (σ , s) zero    = refl
  compsub∋ σ′ (σ , s) (wk∋ i) = compsub∋ σ′ σ i

  -- Kovacs: idlₑₛ
  lidget§ : ∀ {Γ Δ} (τ : Γ ⊢§ Δ) →
            get§ id⊑ τ ≡ τ
  --        id⊑ ◑ τ ≡ τ
  lidget§ ∙       = refl
  lidget§ (τ , t) = (_, t) & lidget§ τ

  compget§ : ∀ {Γ Δ Δ′ Δ″} (ϱ : Δ ⊑ Δ′) (ϱ′ : Δ′ ⊑ Δ″) (τ : Γ ⊢§ Δ″) →
             get§ (ϱ′ ∘⊑ ϱ) τ ≡ (get§ ϱ ∘ get§ ϱ′) τ
  --         (ϱ ○ ϱ′) ◑ τ ≡ ϱ ◑ (ϱ′ ◑ τ)
  compget§ ϱ         stop       ∙       = refl
  compget§ ϱ         (wk⊑ ϱ′)   (τ , t) = compget§ ϱ ϱ′ τ
  compget§ (wk⊑ ϱ)   (lift⊑ ϱ′) (τ , t) = compget§ ϱ ϱ′ τ
  compget§ (lift⊑ ϱ) (lift⊑ ϱ′) (τ , t) = (_, t) & compget§ ϱ ϱ′ τ

  -- Kovacs: assₑₛₑ
  eqrenget§ : ∀ {Γ Γ′ Δ Δ′} (ϱ : Γ ⊑ Γ′) (ϱ′ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
              (get§ ϱ′ ∘ ren§ ϱ) τ ≡ (ren§ ϱ ∘ get§ ϱ′) τ
  --          ϱ′ ◑ (τ ◐ ϱ) ≡ (ϱ′ ◑ τ) ◐ ϱ
  eqrenget§ ϱ stop       ∙       = refl
  eqrenget§ ϱ (wk⊑ ϱ′)   (τ , t) = eqrenget§ ϱ ϱ′ τ
  eqrenget§ ϱ (lift⊑ ϱ′) (τ , t) = (_, ren ϱ t) & eqrenget§ ϱ ϱ′ τ

  eqwkget§ : ∀ {B Γ Δ Δ′} (ϱ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
             (get§ (wk⊑ ϱ) ∘ lift§) τ ≡ (wk§ {B} ∘ get§ ϱ) τ
  --         (wk⊑ ϱ) ◑ (lift§ τ) ≡ wk§ {B} (ϱ ◑ τ)
  eqwkget§ ϱ τ = eqrenget§ (wk⊑ id⊑) ϱ τ

  eqliftget§ : ∀ {B Γ Δ Δ′} (ϱ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
               (get§ (lift⊑ ϱ) ∘ lift§) τ ≡ (lift§ {B} ∘ get§ ϱ) τ
  --           (lift⊑ ϱ) ◑ (lift§ τ) ≡ lift§ {B} (ϱ ◑ τ)
  eqliftget§ ϱ τ = (_, var zero) & eqwkget§ ϱ τ

  -- Kovacs: idrₑₛ; not really identity
  ridget§ : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) →
            get§ ϱ id§ ≡ var§ ϱ
  --        ϱ ◑ id§ ≡ var§ ϱ
  ridget§ stop      = refl
  ridget§ (wk⊑ ϱ)   = eqrenget§ (wk⊑ id⊑) ϱ id§ ⋮ wk§ & ridget§ ϱ
  ridget§ (lift⊑ ϱ) = (_, var zero) & (eqrenget§ (wk⊑ id⊑) ϱ id§ ⋮ wk§ & ridget§ ϱ)


----------------------------------------------------------------------------------------------------

record RenSubKit2Params : Set₁ where
  constructor kit
  field
    rensubkit1 : RenSubKit1Params
  open RenSubKit1Params rensubkit1 public
  open RenSubKit1 rensubkit1 public hiding (rensubkit1)
  field
    eqrensub : ∀ {Γ Ξ Ξ′ A} (ϱ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
               sub (ren§ ϱ σ) t ≡ (ren ϱ ∘ sub σ) t
    --         sub (σ ◐ ϱ) t ≡ (sub σ ⨾ ren ϱ) t
    eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
               sub (get§ ϱ σ) t ≡ (sub σ ∘ ren ϱ) t
    --         sub (ϱ ◑ σ) t ≡ (ren ϱ ⨾ sub σ) t
    lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub id§ t ≡ t

module RenSubKit2 (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  rensubkit2 = ¶

  -- Kovacs: assₛₛₑ
  eqrensub§ : ∀ {Γ Ξ Ξ′ Δ} (ϱ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (τ : Γ ⊢§ Δ) →
              sub§ (ren§ ϱ σ) τ ≡ (ren§ ϱ ∘ sub§ σ) τ
  --          τ ● (σ ◐ ϱ) ≡ (τ ● σ) ◐ ϱ
  eqrensub§ ϱ σ ∙       = refl
  eqrensub§ ϱ σ (τ , t) = _,_ & eqrensub§ ϱ σ τ ⊗ eqrensub ϱ σ t

  -- Kovacs: assₛₑₛ
  eqsubren§ : ∀ {Γ Γ′ Ξ Δ} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
              sub§ (get§ ϱ σ) τ ≡ (sub§ σ ∘ ren§ ϱ) τ
  --          τ ● (ϱ ◑ σ) ≡ (τ ◐ ϱ) ● σ
  eqsubren§ σ ϱ ∙       = refl
  eqsubren§ σ ϱ (τ , t) = _,_ & eqsubren§ σ ϱ τ ⊗ eqsubren σ ϱ t

  -- Kovacs: idrₛ
  lidsub§ : ∀ {Γ Δ} (τ : Γ ⊢§ Δ) →
            sub§ id§ τ ≡ τ
  --        τ ● id§ ≡ τ
  lidsub§ ∙       = refl
  lidsub§ (τ , t) = _,_ & lidsub§ τ ⊗ lidsub t

  eqsub : ∀ {B Γ Ξ A} (σ : Ξ ⊢§ Γ) (s : Ξ ⊢ B) (t : Γ ⊢ A) →
          (sub (σ , s) ∘ wk) t ≡ sub σ t
  eqsub σ s t = eqsubren (σ , s) (wk⊑ id⊑) t ⁻¹
              ⋮ flip sub t & lidget§ σ

  eqsub§ : ∀ {B Γ Ξ Δ} (σ : Ξ ⊢§ Γ) (s : Ξ ⊢ B) (τ : Γ ⊢§ Δ) →
           (sub§ (σ , s) ∘ wk§) τ ≡ sub§ σ τ
  --       (wk§ τ) ● (σ , s) ≡ τ ● σ
  eqsub§ σ s ∙       = refl
  eqsub§ σ s (τ , t) = _,_ & eqsub§ σ s τ ⊗ eqsub σ s t

  eqwksub : ∀ {B Γ Ξ A} (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
            (sub (lift§ σ) ∘ wk) t ≡ (wk {B} ∘ sub σ) t
  eqwksub σ t = eqsubren (lift§ σ) (wk⊑ id⊑) t ⁻¹
              ⋮ flip sub t & (eqwkget§ id⊑ σ ⋮ wk§ & lidget§ σ)
              ⋮ eqrensub (wk⊑ id⊑) σ t

  eqwksub§ : ∀ {B Γ Ξ Δ} (σ : Ξ ⊢§ Γ) (τ : Γ ⊢§ Δ) →
             (sub§ (lift§ σ) ∘ wk§) τ ≡ (wk§ {B} ∘ sub§ σ) τ
  --         (wk§ τ) ● (lift§ σ) ≡ wk§ {B} (τ ● σ)
  eqwksub§ σ ∙       = refl
  eqwksub§ σ (τ , t) = _,_ & eqwksub§ σ τ ⊗ eqwksub σ t

  eqliftsub§ : ∀ {B Γ Ξ Δ} (σ : Ξ ⊢§ Γ) (τ : Γ ⊢§ Δ) →
               (sub§ (lift§ σ) ∘ lift§) τ ≡ (lift§ {B} ∘ sub§ σ) τ
  --           (lift§ τ) ● (lift§ σ) ≡ lift§ {B} (τ ● σ)
  eqliftsub§ σ τ = ((sub§ (lift§ σ) ∘ wk§) τ ,_) & ridsub (lift§ σ) zero
                 ⋮ (_, var zero) & eqwksub§ σ τ

  -- Kovacs: idlₛ
  ridsub§ : ∀ {Γ Ξ} (σ : Ξ ⊢§ Γ) →
            sub§ σ id§ ≡ σ
  --        id§ ● σ ≡ σ
  ridsub§ ∙       = refl
  ridsub§ (σ , s) = ((sub§ (σ , s) ∘ wk§) id§ ,_) & ridsub (σ , s) zero
                  ⋮ (_, s) & (eqsub§ σ s id§ ⋮ ridsub§ σ)


----------------------------------------------------------------------------------------------------

record RenSubKit3Params : Set₁ where
  constructor kit
  field
    rensubkit2 : RenSubKit2Params
  open RenSubKit2Params rensubkit2 public
  open RenSubKit2 rensubkit2 public hiding (rensubkit2)
  field
    compsub : ∀ {Γ Ξ Ξ′ A} (σ′ : Ξ′ ⊢§ Ξ) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
              sub (sub§ σ′ σ) t ≡ (sub σ′ ∘ sub σ) t
    --        sub (σ ● σ′) t ≡ (sub σ ⨾ sub σ′) t

module RenSubKit3 (¶ : RenSubKit3Params) where
  open RenSubKit3Params ¶
  rensubkit3 = ¶

  -- Kovacs: assₛ
  asssub§ : ∀ {Γ Ξ Ξ′ Δ} (σ′ : Ξ′ ⊢§ Ξ) (σ : Ξ ⊢§ Γ) (τ : Γ ⊢§ Δ) →
            (sub§ σ′ ∘ sub§ σ) τ ≡ sub§ (sub§ σ′ σ) τ
  --        (τ ● σ) ● σ′ ≡ τ ● (σ ● σ′)
  asssub§ σ′ σ ∙       = refl
  asssub§ σ′ σ (τ , t) = _,_ & asssub§ σ′ σ τ ⊗ compsub σ′ σ t ⁻¹

  rencut : ∀ {Γ Γ′ A B} (ϱ : Γ ⊑ Γ′) (t₁ : Γ , A ⊢ B) (t₂ : Γ ⊢ A) →
           ren (lift⊑ ϱ) t₁ [ ren ϱ t₂ ] ≡ ren ϱ (t₁ [ t₂ ])
  rencut ϱ t₁ t₂ = eqsubren (id§ , ren ϱ t₂) (lift⊑ ϱ) t₁ ⁻¹
                 ⋮ (flip sub t₁ ∘ (_, ren ϱ t₂)) & (ridget§ ϱ ⋮ ridren§ ϱ ⁻¹)
                 ⋮ eqrensub ϱ (id§ , t₂) t₁

  subcut : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) (t₂ : Γ ⊢ A) →
           sub (lift§ σ) t₁ [ sub σ t₂ ] ≡ sub σ (t₁ [ t₂ ])
  subcut σ t₁ t₂ = compsub (id§ , sub σ t₂) (lift§ σ) t₁ ⁻¹
                 ⋮ flip sub t₁ &
                     ( _,_ & ( eqsubren§ (id§ , sub σ t₂) (wk⊑ id⊑) σ ⁻¹
                             ⋮ flip sub§ σ & lidget§ id§
                             ⋮ lidsub§ σ
                             ⋮ ridsub§ σ ⁻¹
                             )
                           ⊗ ridsub (id§ , sub σ t₂) zero
                     )
                 ⋮ compsub σ (id§ , t₂) t₁


----------------------------------------------------------------------------------------------------
