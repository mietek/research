----------------------------------------------------------------------------------------------------

-- laws of renaming and substitution

module A202401.STLC-Base-RenSub where

open import A202401.STLC-Base public
open import A202401.Kit2 public


----------------------------------------------------------------------------------------------------

lidren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊑ t ≡ t
lidren (var i)     = var & idren∋ i
lidren (⌜λ⌝ t)     = ⌜λ⌝ & lidren t
lidren (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & lidren t₁ ⊗ lidren t₂

compren : ∀ {Γ Γ′ Γ″ A} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
          ren (ϱ′ ∘⊑ ϱ) t ≡ (ren ϱ′ ∘ ren ϱ) t
compren ϱ′ ϱ (var i)     = var & compren∋ ϱ′ ϱ i
compren ϱ′ ϱ (⌜λ⌝ t)     = ⌜λ⌝ & compren (lift⊑ ϱ′) (lift⊑ ϱ) t
compren ϱ′ ϱ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren ϱ′ ϱ t₁ ⊗ compren ϱ′ ϱ t₂

-- not really identity
ridren : ∀ {Γ Γ′ A} (ϱ : Γ ⊑ Γ′) (i : Γ ∋ A) → ren ϱ (var i) ≡ var (ren∋ ϱ i)
ridren ϱ i = refl

-- not really identity
ridsub : ∀ {Γ Ξ A} (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) → sub σ (var i) ≡ sub∋ σ i
ridsub σ i = refl

open RenSubKit1 (kit subkit lidren compren ridren ridsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (ϱ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
           sub (ren§ ϱ σ) t ≡ (ren ϱ ∘ sub σ) t
eqrensub ϱ σ (var i)     = eqrensub∋ ϱ σ i
eqrensub ϱ σ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftren§ ϱ σ ⁻¹
                                 ⋮ eqrensub (lift⊑ ϱ) (lift§ σ) t
                                 )
eqrensub ϱ σ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqrensub ϱ σ t₁ ⊗ eqrensub ϱ σ t₂

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
           sub (get§ ϱ σ) t ≡ (sub σ ∘ ren ϱ) t
eqsubren σ ϱ (var i)     = eqsubren∋ σ ϱ i
eqsubren σ ϱ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftget§ ϱ σ ⁻¹
                                 ⋮ eqsubren (lift§ σ) (lift⊑ ϱ) t
                                 )
eqsubren σ ϱ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren σ ϱ t₁ ⊗ eqsubren σ ϱ t₂

-- Kovacs: Tm-idₛ
lidsub : ∀ {Γ A} (t : Γ ⊢ A) → sub id§ t ≡ t
lidsub (var i)     = idsub∋ i
lidsub (⌜λ⌝ t)     = ⌜λ⌝ & lidsub t
lidsub (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & lidsub t₁ ⊗ lidsub t₂

open RenSubKit2 (kit rensubkit1 eqrensub eqsubren lidsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-∘ₛ
compsub : ∀ {Γ Ξ Ξ′ A} (σ′ : Ξ′ ⊢§ Ξ) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
          sub (sub§ σ′ σ) t ≡ (sub σ′ ∘ sub σ) t
compsub σ′ σ (var i)     = compsub∋ σ′ σ i
compsub σ′ σ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftsub§ σ′ σ ⁻¹
                                 ⋮ compsub (lift§ σ′) (lift§ σ) t
                                 )
compsub σ′ σ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compsub σ′ σ t₁ ⊗ compsub σ′ σ t₂

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
