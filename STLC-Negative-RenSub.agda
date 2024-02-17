----------------------------------------------------------------------------------------------------

-- laws of renaming and substitution

module STLC-Negative-RenSub where

open import STLC-Negative public
open import Kit2 public


----------------------------------------------------------------------------------------------------

lidren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊑ t ≡ t
lidren (var i)     = var & idren∋ i
lidren (⌜λ⌝ t)     = ⌜λ⌝ & lidren t
lidren (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & lidren t₁ ⊗ lidren t₂
lidren (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & lidren t₁ ⊗ lidren t₂
lidren (⌜fst⌝ t)   = ⌜fst⌝ & lidren t
lidren (⌜snd⌝ t)   = ⌜snd⌝ & lidren t
lidren ⌜unit⌝      = refl

compren : ∀ {Γ Γ′ Γ″ A} (ρ′ : Γ′ ⊑ Γ″) (ρ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
          ren (ρ′ ∘⊑ ρ) t ≡ (ren ρ′ ∘ ren ρ) t
compren ρ′ ρ (var i)     = var & compren∋ ρ′ ρ i
compren ρ′ ρ (⌜λ⌝ t)     = ⌜λ⌝ & compren (lift⊑ ρ′) (lift⊑ ρ) t
compren ρ′ ρ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren ρ′ ρ t₁ ⊗ compren ρ′ ρ t₂
compren ρ′ ρ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & compren ρ′ ρ t₁ ⊗ compren ρ′ ρ t₂
compren ρ′ ρ (⌜fst⌝ t)   = ⌜fst⌝ & compren ρ′ ρ t
compren ρ′ ρ (⌜snd⌝ t)   = ⌜snd⌝ & compren ρ′ ρ t
compren ρ′ ρ ⌜unit⌝      = refl

-- not really identity
ridren : ∀ {Γ Γ′ A} (ρ : Γ ⊑ Γ′) (i : Γ ∋ A) → ren ρ (var i) ≡ var (ren∋ ρ i)
ridren ρ i = refl

-- not really identity
ridsub : ∀ {Γ Ξ A} (σ : Ξ ⊢§ Γ) (i : Γ ∋ A) → sub σ (var i) ≡ sub∋ σ i
ridsub σ i = refl

open RenSubKit1 (kit subkit lidren compren ridren ridsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (ρ : Ξ ⊑ Ξ′) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
           sub (ren§ ρ σ) t ≡ (ren ρ ∘ sub σ) t
eqrensub ρ σ (var i)     = eqrensub∋ ρ σ i
eqrensub ρ σ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftren§ ρ σ ⁻¹
                                 ⋮ eqrensub (lift⊑ ρ) (lift§ σ) t
                                 )
eqrensub ρ σ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqrensub ρ σ t₁ ⊗ eqrensub ρ σ t₂
eqrensub ρ σ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqrensub ρ σ t₁ ⊗ eqrensub ρ σ t₂
eqrensub ρ σ (⌜fst⌝ t)   = ⌜fst⌝ & eqrensub ρ σ t
eqrensub ρ σ (⌜snd⌝ t)   = ⌜snd⌝ & eqrensub ρ σ t
eqrensub ρ σ ⌜unit⌝      = refl

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ρ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
           sub (get§ ρ σ) t ≡ (sub σ ∘ ren ρ) t
eqsubren σ ρ (var i)     = eqsubren∋ σ ρ i
eqsubren σ ρ (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftget§ ρ σ ⁻¹
                                 ⋮ eqsubren (lift§ σ) (lift⊑ ρ) t
                                 )
eqsubren σ ρ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren σ ρ t₁ ⊗ eqsubren σ ρ t₂
eqsubren σ ρ (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqsubren σ ρ t₁ ⊗ eqsubren σ ρ t₂
eqsubren σ ρ (⌜fst⌝ t)   = ⌜fst⌝ & eqsubren σ ρ t
eqsubren σ ρ (⌜snd⌝ t)   = ⌜snd⌝ & eqsubren σ ρ t
eqsubren σ ρ ⌜unit⌝      = refl

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
