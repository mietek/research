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
    compren : ∀ {Γ Γ′ Γ″ A} (ρ′ : Γ′ ⊑ Γ″) (ρ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
              ren (ρ′ ∘⊑ ρ) t ≡ (ren ρ′ ∘ ren ρ) t
    --        ren (ρ ○ ρ′) t ≡ (ren ρ′ ∘ ren ρ) t
    ridren  : ∀ {Γ Γ′ A} (ρ : Γ ⊑ Γ′) (i : Γ ∋ A) → ren ρ (var i) ≡ var (ren∋ ρ i)
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
  compren§ : ∀ {Γ Γ′ Γ″ Δ} (ρ′ : Γ′ ⊑ Γ″) (ρ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
             ren§ (ρ′ ∘⊑ ρ) τ ≡ (ren§ ρ′ ∘ ren§ ρ) τ
  --         τ ◐ (ρ ○ ρ′) ≡ (τ ◐ ρ) ◐ ρ′
  compren§ ρ′ ρ ∙       = refl
  compren§ ρ′ ρ (τ , t) = _,_ & compren§ ρ′ ρ τ ⊗ compren ρ′ ρ t

  eqwkren : ∀ {B Γ Γ′ A} (ρ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
            (ren (lift⊑ ρ) ∘ wk) t ≡ (wk {B} ∘ ren ρ) t
  eqwkren ρ t = compren (lift⊑ ρ) (wk⊑ id⊑) t ⁻¹
              ⋮ (flip ren t ∘ wk⊑) & (rid⊑ ρ ⋮ lid⊑ ρ ⁻¹)
              ⋮ compren (wk⊑ id⊑) ρ t

  eqwkren§ : ∀ {B Γ Γ′ Δ} (ρ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
             (ren§ (lift⊑ ρ) ∘ wk§) τ ≡ (wk§ {B} ∘ ren§ ρ) τ
  --         (wk§ τ) ◐ (lift⊑ ρ) ≡ wk§ {B} (τ ◐ ρ)
  eqwkren§ ρ ∙       = refl
  eqwkren§ ρ (τ , t) = _,_ & eqwkren§ ρ τ ⊗ eqwkren ρ t

  eqliftren§ : ∀ {B Γ Γ′ Δ} (ρ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
               (ren§ (lift⊑ ρ) ∘ lift§) τ ≡ (lift§ {B} ∘ ren§ ρ) τ
  --           (lift§ τ) ◐ (lift⊑ ρ) ≡ lift§ {B} (τ ◐ ρ)
  eqliftren§ ρ τ = ((ren§ (lift⊑ ρ) ∘ wk§) τ ,_) & ridren (lift⊑ ρ) zero
                 ⋮ (_, var zero) & eqwkren§ ρ τ

  -- Kovacs: idlₛₑ; not really identity
  ridren§ : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) →
            ren§ ρ id§ ≡ var§ ρ
  --        id§ ◐ ρ ≡ var§ ρ
  ridren§ stop      = refl
  ridren§ (wk⊑ ρ)   = (flip ren§ id§ ∘ wk⊑) & lid⊑ ρ ⁻¹
                    ⋮ compren§ (wk⊑ id⊑) ρ id§
                    ⋮ wk§ & ridren§ ρ
  ridren§ (lift⊑ ρ) = ((ren§ (lift⊑ ρ) ∘ wk§) id§ ,_) & ridren (lift⊑ ρ) zero
                    ⋮ (_, var zero) & (eqwkren§ ρ id§ ⋮ wk§ & ridren§ ρ)

  -- Kovacs: ∈-ₛ∘ₑ
  eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (ρ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) →
              sub∋ (ren§ ρ σ) i ≡ (ren ρ ∘ sub∋ σ) i
  --          sub∋ (σ ◐ ρ) i ≡ (sub∋ σ ⨾ ren ρ) i
  eqrensub∋ ρ (σ , s) zero    = refl
  eqrensub∋ ρ (σ , s) (wk∋ i) = eqrensub∋ ρ σ i

  -- Kovacs: ∈-ₑ∘ₛ
  eqsubren∋ : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ρ : Γ ⊑ Γ′) (i : Γ ∋ A) →
              sub∋ (get§ ρ σ) i ≡ (sub∋ σ ∘ ren∋ ρ) i
  --          sub∋ (ρ ◑ σ) i ≡ (ren∋ ρ ⨾ sub∋ σ) i
  eqsubren∋ ∙       stop      i       = refl
  eqsubren∋ (σ , s) (wk⊑ ρ)   i       = eqsubren∋ σ ρ i
  eqsubren∋ (σ , s) (lift⊑ ρ) zero    = refl
  eqsubren∋ (σ , s) (lift⊑ ρ) (wk∋ i) = eqsubren∋ σ ρ i

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

  compget§ : ∀ {Γ Δ Δ′ Δ″} (ρ : Δ ⊑ Δ′) (ρ′ : Δ′ ⊑ Δ″) (τ : Γ ⊢§ Δ″) →
             get§ (ρ′ ∘⊑ ρ) τ ≡ (get§ ρ ∘ get§ ρ′) τ
  --         (ρ ○ ρ′) ◑ τ ≡ ρ ◑ (ρ′ ◑ τ)
  compget§ ρ         stop       ∙       = refl
  compget§ ρ         (wk⊑ ρ′)   (τ , t) = compget§ ρ ρ′ τ
  compget§ (wk⊑ ρ)   (lift⊑ ρ′) (τ , t) = compget§ ρ ρ′ τ
  compget§ (lift⊑ ρ) (lift⊑ ρ′) (τ , t) = (_, t) & compget§ ρ ρ′ τ

  -- Kovacs: assₑₛₑ
  eqrenget§ : ∀ {Γ Γ′ Δ Δ′} (ρ : Γ ⊑ Γ′) (ρ′ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
              (get§ ρ′ ∘ ren§ ρ) τ ≡ (ren§ ρ ∘ get§ ρ′) τ
  --          ρ′ ◑ (τ ◐ ρ) ≡ (ρ′ ◑ τ) ◐ ρ
  eqrenget§ ρ stop       ∙       = refl
  eqrenget§ ρ (wk⊑ ρ′)   (τ , t) = eqrenget§ ρ ρ′ τ
  eqrenget§ ρ (lift⊑ ρ′) (τ , t) = (_, ren ρ t) & eqrenget§ ρ ρ′ τ

  eqwkget§ : ∀ {B Γ Δ Δ′} (ρ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
             (get§ (wk⊑ ρ) ∘ lift§) τ ≡ (wk§ {B} ∘ get§ ρ) τ
  --         (wk⊑ ρ) ◑ (lift§ τ) ≡ wk§ {B} (ρ ◑ τ)
  eqwkget§ ρ τ = eqrenget§ (wk⊑ id⊑) ρ τ

  eqliftget§ : ∀ {B Γ Δ Δ′} (ρ : Δ ⊑ Δ′) (τ : Γ ⊢§ Δ′) →
               (get§ (lift⊑ ρ) ∘ lift§) τ ≡ (lift§ {B} ∘ get§ ρ) τ
  --           (lift⊑ ρ) ◑ (lift§ τ) ≡ lift§ {B} (ρ ◑ τ)
  eqliftget§ ρ τ = (_, var zero) & eqwkget§ ρ τ

  -- Kovacs: idrₑₛ; not really identity
  ridget§ : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) →
            get§ ρ id§ ≡ var§ ρ
  --        ρ ◑ id§ ≡ var§ ρ
  ridget§ stop      = refl
  ridget§ (wk⊑ ρ)   = eqrenget§ (wk⊑ id⊑) ρ id§ ⋮ wk§ & ridget§ ρ
  ridget§ (lift⊑ ρ) = (_, var zero) & (eqrenget§ (wk⊑ id⊑) ρ id§ ⋮ wk§ & ridget§ ρ)


----------------------------------------------------------------------------------------------------

record RenSubKit2Params : Set₁ where
  constructor kit
  field
    rensubkit1 : RenSubKit1Params
  open RenSubKit1Params rensubkit1 public
  open RenSubKit1 rensubkit1 public hiding (rensubkit1)
  field
    eqrensub : ∀ {Γ Ξ Ξ′ A} (ρ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
               sub (ren§ ρ σ) t ≡ (ren ρ ∘ sub σ) t
    --         sub (σ ◐ ρ) t ≡ (sub σ ⨾ ren ρ) t
    eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ρ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
               sub (get§ ρ σ) t ≡ (sub σ ∘ ren ρ) t
    --         sub (ρ ◑ σ) t ≡ (ren ρ ⨾ sub σ) t
    lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub id§ t ≡ t

module RenSubKit2 (¶ : RenSubKit2Params) where
  open RenSubKit2Params ¶
  rensubkit2 = ¶

  -- Kovacs: assₛₛₑ
  eqrensub§ : ∀ {Γ Ξ Ξ′ Δ} (ρ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (τ : Γ ⊢§ Δ) →
              sub§ (ren§ ρ σ) τ ≡ (ren§ ρ ∘ sub§ σ) τ
  --          τ ● (σ ◐ ρ) ≡ (τ ● σ) ◐ ρ
  eqrensub§ ρ σ ∙       = refl
  eqrensub§ ρ σ (τ , t) = _,_ & eqrensub§ ρ σ τ ⊗ eqrensub ρ σ t

  -- Kovacs: assₛₑₛ
  eqsubren§ : ∀ {Γ Γ′ Ξ Δ} (σ : Ξ ⊢§ Γ′) (ρ : Γ ⊑ Γ′) (τ : Γ ⊢§ Δ) →
              sub§ (get§ ρ σ) τ ≡ (sub§ σ ∘ ren§ ρ) τ
  --          τ ● (ρ ◑ σ) ≡ (τ ◐ ρ) ● σ
  eqsubren§ σ ρ ∙       = refl
  eqsubren§ σ ρ (τ , t) = _,_ & eqsubren§ σ ρ τ ⊗ eqsubren σ ρ t

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

  rencut : ∀ {Γ Γ′ A B} (ρ : Γ ⊑ Γ′) (t₁ : Γ , A ⊢ B) (t₂ : Γ ⊢ A) →
           ren (lift⊑ ρ) t₁ [ ren ρ t₂ ] ≡ ren ρ (t₁ [ t₂ ])
  rencut ρ t₁ t₂ = eqsubren (id§ , ren ρ t₂) (lift⊑ ρ) t₁ ⁻¹
                 ⋮ (flip sub t₁ ∘ (_, ren ρ t₂)) & (ridget§ ρ ⋮ ridren§ ρ ⁻¹)
                 ⋮ eqrensub ρ (id§ , t₂) t₁

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
