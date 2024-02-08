----------------------------------------------------------------------------------------------------

-- categorical laws for renaming and substitution

module STLC-Naturals-RenSub where

open import STLC-Naturals public
open import Kit2 public


----------------------------------------------------------------------------------------------------

lidren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
lidren (var i)          = var & idren∋ i
lidren (⌜λ⌝ t)          = ⌜λ⌝ & lidren t
lidren (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & lidren t₁ ⊗ lidren t₂
lidren ⌜zero⌝           = refl
lidren (⌜suc⌝ t)        = ⌜suc⌝ & lidren t
lidren (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & lidren tₙ ⊗ lidren t₀ ⊗ lidren tₛ

compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
          ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t
compren e′ e (var i)          = var & compren∋ e′ e i
compren e′ e (⌜λ⌝ t)          = ⌜λ⌝ & compren (lift⊆ e′) (lift⊆ e) t
compren e′ e (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂
compren e′ e ⌜zero⌝           = refl
compren e′ e (⌜suc⌝ t)        = ⌜suc⌝ & compren e′ e t
compren e′ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compren e′ e tₙ ⊗ compren e′ e t₀
                                  ⊗ compren (lift⊆² e′) (lift⊆² e) tₛ

-- not really identity
ridren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
ridren e i = refl

-- not really identity
ridsub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i
ridsub ss i = refl

open RenSubKit1 (kit subkit lidren compren ridren ridsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
           sub (ren* e ss) t ≡ (ren e ∘ sub ss) t
eqrensub e ss (var i)          = eqrensub∋ e ss i
eqrensub e ss (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftren* e ss ⁻¹
                                       ⋮ eqrensub (lift⊆ e) (lift* ss) t
                                       )
eqrensub e ss (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqrensub e ss t₁ ⊗ eqrensub e ss t₂
eqrensub e ss ⌜zero⌝           = refl
eqrensub e ss (⌜suc⌝ t)        = ⌜suc⌝ & eqrensub e ss t
eqrensub e ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqrensub e ss tₙ ⊗ eqrensub e ss t₀
                                   ⊗ ( flip sub tₛ & ( lift* & eqliftren* e ss ⁻¹
                                                     ⋮ eqliftren* (lift⊆ e) (lift* ss) ⁻¹
                                                     )
                                     ⋮ eqrensub (lift⊆² e) (lift*² ss) tₛ
                                     )

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
           sub (get* e ss) t ≡ (sub ss ∘ ren e) t
eqsubren ss e (var i)          = eqsubren∋ ss e i
eqsubren ss e (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftget* e ss ⁻¹
                                       ⋮ eqsubren (lift* ss) (lift⊆ e) t
                                       )
eqsubren ss e (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqsubren ss e t₁ ⊗ eqsubren ss e t₂
eqsubren ss e ⌜zero⌝           = refl
eqsubren ss e (⌜suc⌝ t)        = ⌜suc⌝ & eqsubren ss e t
eqsubren ss e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqsubren ss e tₙ ⊗ eqsubren ss e t₀
                                   ⊗ ( flip sub tₛ & ( lift* & eqliftget* e ss ⁻¹
                                                     ⋮ eqliftget* (lift⊆ e) (lift* ss) ⁻¹
                                                     )
                                     ⋮ eqsubren (lift*² ss) (lift⊆² e) tₛ
                                     )

-- Kovacs: Tm-idₛ
lidsub : ∀ {Γ A} (t : Γ ⊢ A) → sub id* t ≡ t
lidsub (var i)          = idsub∋ i
lidsub (⌜λ⌝ t)          = ⌜λ⌝ & lidsub t
lidsub (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & lidsub t₁ ⊗ lidsub t₂
lidsub ⌜zero⌝           = refl
lidsub (⌜suc⌝ t)        = ⌜suc⌝ & lidsub t
lidsub (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & lidsub tₙ ⊗ lidsub t₀ ⊗ lidsub tₛ

open RenSubKit2 (kit rensubkit1 eqrensub eqsubren lidsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-∘ₛ
compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          sub (sub* ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
compsub ss′ ss (var i)          = compsub∋ ss′ ss i
compsub ss′ ss (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftsub* ss′ ss ⁻¹
                                        ⋮ compsub (lift* ss′) (lift* ss) t
                                        )
compsub ss′ ss (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compsub ss′ ss t₁ ⊗ compsub ss′ ss t₂
compsub ss′ ss ⌜zero⌝           = refl
compsub ss′ ss (⌜suc⌝ t)        = ⌜suc⌝ & compsub ss′ ss t
compsub ss′ ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compsub ss′ ss tₙ ⊗ compsub ss′ ss t₀
                                    ⊗ ( flip sub tₛ & ( lift* & eqliftsub* ss′ ss ⁻¹
                                                      ⋮ eqliftsub* (lift* ss′) (lift* ss) ⁻¹
                                                      )
                                      ⋮ compsub (lift*² ss′) (lift*² ss) tₛ
                                      )

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
