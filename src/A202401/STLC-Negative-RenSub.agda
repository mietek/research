----------------------------------------------------------------------------------------------------

-- laws of renaming and substitution

module A202401.STLC-Negative-RenSub where

open import A202401.STLC-Negative public
open import A202401.Kit2 public


----------------------------------------------------------------------------------------------------

lidren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊑ t ≡ t
lidren (var i)     = var & idren∋ i
lidren (⌜λ⌝ t)     = ⌜λ⌝ & lidren t
lidren (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & lidren t₁ ⊗ lidren t₂
lidren (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & lidren t₁ ⊗ lidren t₂
lidren (⌜fst⌝ t)   = ⌜fst⌝ & lidren t
lidren (⌜snd⌝ t)   = ⌜snd⌝ & lidren t
lidren ⌜unit⌝      = refl

compren : ∀ {Γ Γ′ Γ″ A} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
          ren (ϱ′ ∘⊑ ϱ) t ≡ (ren ϱ′ ∘ ren ϱ) t
compren ϱ′ ϱ (var i)     = var & compren∋ ϱ′ ϱ i
compren ϱ′ ϱ (⌜λ⌝ t)     = ⌜λ⌝ & compren (lift⊑ ϱ′) (lift⊑ ϱ) t
compren ϱ′ ϱ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren ϱ′ ϱ t₁ ⊗ compren ϱ′ ϱ t₂
compren ϱ′ ϱ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & compren ϱ′ ϱ t₁ ⊗ compren ϱ′ ϱ t₂
compren ϱ′ ϱ (⌜fst⌝ t)   = ⌜fst⌝ & compren ϱ′ ϱ t
compren ϱ′ ϱ (⌜snd⌝ t)   = ⌜snd⌝ & compren ϱ′ ϱ t
compren ϱ′ ϱ ⌜unit⌝      = refl

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
eqrensub ϱ σ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqrensub ϱ σ t₁ ⊗ eqrensub ϱ σ t₂
eqrensub ϱ σ (⌜fst⌝ t)   = ⌜fst⌝ & eqrensub ϱ σ t
eqrensub ϱ σ (⌜snd⌝ t)   = ⌜snd⌝ & eqrensub ϱ σ t
eqrensub ϱ σ ⌜unit⌝      = refl

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
           sub (get§ ϱ σ) t ≡ (sub σ ∘ ren ϱ) t
eqsubren σ ϱ (var i)     = eqsubren∋ σ ϱ i
eqsubren σ ϱ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftget§ ϱ σ ⁻¹
                                 ⋮ eqsubren (lift§ σ) (lift⊑ ϱ) t
                                 )
eqsubren σ ϱ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren σ ϱ t₁ ⊗ eqsubren σ ϱ t₂
eqsubren σ ϱ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqsubren σ ϱ t₁ ⊗ eqsubren σ ϱ t₂
eqsubren σ ϱ (⌜fst⌝ t)   = ⌜fst⌝ & eqsubren σ ϱ t
eqsubren σ ϱ (⌜snd⌝ t)   = ⌜snd⌝ & eqsubren σ ϱ t
eqsubren σ ϱ ⌜unit⌝      = refl

-- Kovacs: Tm-idₛ
lidsub : ∀ {Γ A} (t : Γ ⊢ A) → sub id§ t ≡ t
lidsub (var i)     = idsub∋ i
lidsub (⌜λ⌝ t)     = ⌜λ⌝ & lidsub t
lidsub (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & lidsub t₁ ⊗ lidsub t₂
lidsub (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & lidsub t₁ ⊗ lidsub t₂
lidsub (⌜fst⌝ t)   = ⌜fst⌝ & lidsub t
lidsub (⌜snd⌝ t)   = ⌜snd⌝ & lidsub t
lidsub ⌜unit⌝      = refl

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
compsub σ′ σ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & compsub σ′ σ t₁ ⊗ compsub σ′ σ t₂
compsub σ′ σ (⌜fst⌝ t)   = ⌜fst⌝ & compsub σ′ σ t
compsub σ′ σ (⌜snd⌝ t)   = ⌜snd⌝ & compsub σ′ σ t
compsub σ′ σ ⌜unit⌝      = refl

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
