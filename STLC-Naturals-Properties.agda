module STLC-Naturals-Properties where

open import STLC-Naturals public
open import Kit2 public


----------------------------------------------------------------------------------------------------

ridren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
ridren (var i)          = var & idren∋ i
ridren (⌜λ⌝ t)          = ⌜λ⌝ & ridren t
ridren (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & ridren t₁ ⊗ ridren t₂
ridren ⌜zero⌝           = refl
ridren (⌜suc⌝ t)        = ⌜suc⌝ & ridren t
ridren (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & ridren tₙ ⊗ ridren t₀ ⊗ ridren tₛ

-- not really identity
lidren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
lidren e i = refl

compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
          ren (e ∘⊆ e′) t ≡ (ren e′ ∘ ren e) t
compren e′ e (var i)          = var & compren∋ e′ e i
compren e′ e (⌜λ⌝ t)          = ⌜λ⌝ & compren (lift⊆ e′) (lift⊆ e) t
compren e′ e (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂
compren e′ e ⌜zero⌝           = refl
compren e′ e (⌜suc⌝ t)        = ⌜suc⌝ & compren e′ e t
compren e′ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compren e′ e tₙ ⊗ compren e′ e t₀
                                  ⊗ compren (lift⊆ (lift⊆ e′)) (lift⊆ (lift⊆ e)) tₛ

open RenSubKit1 (kit subkit ridren lidren compren) public


----------------------------------------------------------------------------------------------------

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
                                     ⋮ eqsubren (lift* (lift* ss)) (lift⊆ (lift⊆ e)) tₛ
                                     )

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
                                     ⋮ eqrensub (lift⊆ (lift⊆ e)) (lift* (lift* ss)) tₛ
                                     )

-- Kovacs: Tm-idₛ
ridsub : ∀ {Γ A} (t : Γ ⊢ A) → sub id* t ≡ t
ridsub (var i)          = idsub∋ i
ridsub (⌜λ⌝ t)          = ⌜λ⌝ & ridsub t
ridsub (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & ridsub t₁ ⊗ ridsub t₂
ridsub ⌜zero⌝           = refl
ridsub (⌜suc⌝ t)        = ⌜suc⌝ & ridsub t
ridsub (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & ridsub tₙ ⊗ ridsub t₀ ⊗ ridsub tₛ

-- not really identity
lidsub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i
lidsub ss i = refl

open RenSubKit2 (kit rensubkit1 eqsubren eqrensub ridsub lidsub) public


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
                                      ⋮ compsub (lift* (lift* ss′)) (lift* (lift* ss)) tₛ
                                      )

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
