----------------------------------------------------------------------------------------------------

-- laws of renaming and substitution

module STLC-Naturals-RenSub where

open import STLC-Naturals public
open import Kit2 public


----------------------------------------------------------------------------------------------------

lidren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊑ t ≡ t
lidren (var i)          = var & idren∋ i
lidren (⌜λ⌝ t)          = ⌜λ⌝ & lidren t
lidren (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & lidren t₁ ⊗ lidren t₂
lidren ⌜zero⌝           = refl
lidren (⌜suc⌝ t)        = ⌜suc⌝ & lidren t
lidren (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & lidren tₙ ⊗ lidren t₀ ⊗ lidren tₛ

compren : ∀ {Γ Γ′ Γ″ A} (ϱ′ : Γ′ ⊑ Γ″) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
          ren (ϱ′ ∘⊑ ϱ) t ≡ (ren ϱ′ ∘ ren ϱ) t
compren ϱ′ ϱ (var i)          = var & compren∋ ϱ′ ϱ i
compren ϱ′ ϱ (⌜λ⌝ t)          = ⌜λ⌝ & compren (lift⊑ ϱ′) (lift⊑ ϱ) t
compren ϱ′ ϱ (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compren ϱ′ ϱ t₁ ⊗ compren ϱ′ ϱ t₂
compren ϱ′ ϱ ⌜zero⌝           = refl
compren ϱ′ ϱ (⌜suc⌝ t)        = ⌜suc⌝ & compren ϱ′ ϱ t
compren ϱ′ ϱ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compren ϱ′ ϱ tₙ ⊗ compren ϱ′ ϱ t₀
                                  ⊗ compren (lift⊑ (lift⊑ ϱ′)) (lift⊑ (lift⊑ ϱ)) tₛ

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
eqrensub ϱ σ (var i)          = eqrensub∋ ϱ σ i
eqrensub ϱ σ (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftren§ ϱ σ ⁻¹
                                      ⋮ eqrensub (lift⊑ ϱ) (lift§ σ) t
                                      )
eqrensub ϱ σ (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqrensub ϱ σ t₁ ⊗ eqrensub ϱ σ t₂
eqrensub ϱ σ ⌜zero⌝           = refl
eqrensub ϱ σ (⌜suc⌝ t)        = ⌜suc⌝ & eqrensub ϱ σ t
eqrensub ϱ σ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqrensub ϱ σ tₙ ⊗ eqrensub ϱ σ t₀
                                  ⊗ ( flip sub tₛ & ( lift§ & eqliftren§ ϱ σ ⁻¹
                                                    ⋮ eqliftren§ (lift⊑ ϱ) (lift§ σ) ⁻¹
                                                    )
                                    ⋮ eqrensub (lift⊑ (lift⊑ ϱ)) (lift§ (lift§ σ)) tₛ
                                    )

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (σ : Ξ ⊢§ Γ′) (ϱ : Γ ⊑ Γ′) (t : Γ ⊢ A) →
           sub (get§ ϱ σ) t ≡ (sub σ ∘ ren ϱ) t
eqsubren σ ϱ (var i)          = eqsubren∋ σ ϱ i
eqsubren σ ϱ (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftget§ ϱ σ ⁻¹
                                      ⋮ eqsubren (lift§ σ) (lift⊑ ϱ) t
                                      )
eqsubren σ ϱ (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqsubren σ ϱ t₁ ⊗ eqsubren σ ϱ t₂
eqsubren σ ϱ ⌜zero⌝           = refl
eqsubren σ ϱ (⌜suc⌝ t)        = ⌜suc⌝ & eqsubren σ ϱ t
eqsubren σ ϱ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqsubren σ ϱ tₙ ⊗ eqsubren σ ϱ t₀
                                  ⊗ ( flip sub tₛ & ( lift§ & eqliftget§ ϱ σ ⁻¹
                                                    ⋮ eqliftget§ (lift⊑ ϱ) (lift§ σ) ⁻¹
                                                    )
                                    ⋮ eqsubren (lift§ (lift§ σ)) (lift⊑ (lift⊑ ϱ)) tₛ
                                    )

-- Kovacs: Tm-idₛ
lidsub : ∀ {Γ A} (t : Γ ⊢ A) → sub id§ t ≡ t
lidsub (var i)          = idsub∋ i
lidsub (⌜λ⌝ t)          = ⌜λ⌝ & lidsub t
lidsub (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & lidsub t₁ ⊗ lidsub t₂
lidsub ⌜zero⌝           = refl
lidsub (⌜suc⌝ t)        = ⌜suc⌝ & lidsub t
lidsub (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & lidsub tₙ ⊗ lidsub t₀ ⊗ lidsub tₛ

open RenSubKit2 (kit rensubkit1 eqrensub eqsubren lidsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-∘ₛ
compsub : ∀ {Γ Ξ Ξ′ A} (σ′ : Ξ′ ⊢§ Ξ) (σ : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
          sub (sub§ σ′ σ) t ≡ (sub σ′ ∘ sub σ) t
compsub σ′ σ (var i)          = compsub∋ σ′ σ i
compsub σ′ σ (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftsub§ σ′ σ ⁻¹
                                      ⋮ compsub (lift§ σ′) (lift§ σ) t
                                      )
compsub σ′ σ (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compsub σ′ σ t₁ ⊗ compsub σ′ σ t₂
compsub σ′ σ ⌜zero⌝           = refl
compsub σ′ σ (⌜suc⌝ t)        = ⌜suc⌝ & compsub σ′ σ t
compsub σ′ σ (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compsub σ′ σ tₙ ⊗ compsub σ′ σ t₀
                                   ⊗ ( flip sub tₛ & ( lift§ & eqliftsub§ σ′ σ ⁻¹
                                                     ⋮ eqliftsub§ (lift§ σ′) (lift§ σ) ⁻¹
                                                     )
                                     ⋮ compsub (lift§ (lift§ σ′)) (lift§ (lift§ σ)) tₛ
                                     )

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
