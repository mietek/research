module STLC-Naturals-Properties where

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

-- not really identity
ridren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
ridren e i = refl

compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
          ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t
compren e′ e (var i)          = var & compren∋ e′ e i
compren e′ e (⌜λ⌝ t)          = ⌜λ⌝ & compren (keep e′) (keep e) t
compren e′ e (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂
compren e′ e ⌜zero⌝           = refl
compren e′ e (⌜suc⌝ t)        = ⌜suc⌝ & compren e′ e t
compren e′ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compren e′ e tₙ ⊗ compren e′ e t₀
                                  ⊗ compren (keep (keep e′)) (keep (keep e)) tₛ

rsk1! = rensubkit1 sk! lidren ridren compren
open RenSubKit1 rsk1! public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
           sub (gets e ss) t ≡ (sub ss ∘ ren e) t
eqsubren ss e (var i)          = eqsubren∋ ss e i
eqsubren ss e (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftgets e ss ⁻¹
                                       ⋮ eqsubren (lifts ss) (keep e) t
                                       )
eqsubren ss e (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqsubren ss e t₁ ⊗ eqsubren ss e t₂
eqsubren ss e ⌜zero⌝           = refl
eqsubren ss e (⌜suc⌝ t)        = ⌜suc⌝ & eqsubren ss e t
eqsubren ss e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqsubren ss e tₙ ⊗ eqsubren ss e t₀
                                   ⊗ ( flip sub tₛ & ( lifts & eqliftgets e ss ⁻¹
                                                     ⋮ eqliftgets (keep e) (lifts ss) ⁻¹
                                                     )
                                     ⋮ eqsubren (lifts (lifts ss)) (keep (keep e)) tₛ
                                     )

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
           sub (rens e ss) t ≡ (ren e ∘ sub ss) t
eqrensub e ss (var i)          = eqrensub∋ e ss i
eqrensub e ss (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftrens e ss ⁻¹
                                       ⋮ eqrensub (keep e) (lifts ss) t
                                       )
eqrensub e ss (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & eqrensub e ss t₁ ⊗ eqrensub e ss t₂
eqrensub e ss ⌜zero⌝           = refl
eqrensub e ss (⌜suc⌝ t)        = ⌜suc⌝ & eqrensub e ss t
eqrensub e ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & eqrensub e ss tₙ ⊗ eqrensub e ss t₀
                                   ⊗ ( flip sub tₛ & ( lifts & eqliftrens e ss ⁻¹
                                                     ⋮ eqliftrens (keep e) (lifts ss) ⁻¹
                                                     )
                                     ⋮ eqrensub (keep (keep e)) (lifts (lifts ss)) tₛ
                                     )

-- Kovacs: Tm-idₛ
lidsub : ∀ {Γ A} (t : Γ ⊢ A) → sub ids t ≡ t
lidsub (var i)          = idsub∋ i
lidsub (⌜λ⌝ t)          = ⌜λ⌝ & lidsub t
lidsub (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & lidsub t₁ ⊗ lidsub t₂
lidsub ⌜zero⌝           = refl
lidsub (⌜suc⌝ t)        = ⌜suc⌝ & lidsub t
lidsub (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & lidsub tₙ ⊗ lidsub t₀ ⊗ lidsub tₛ

-- not really identity
ridsub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i
ridsub ss i = refl

rsk2! = rensubkit2 rsk1! eqsubren eqrensub lidsub ridsub
open RenSubKit2 rsk2! public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-∘ₛ
compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          sub (subs ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
compsub ss′ ss (var i)          = compsub∋ ss′ ss i
compsub ss′ ss (⌜λ⌝ t)          = ⌜λ⌝ & ( flip sub t & eqliftsubs ss′ ss ⁻¹
                                        ⋮ compsub (lifts ss′) (lifts ss) t
                                        )
compsub ss′ ss (t₁ ⌜$⌝ t₂)      = _⌜$⌝_ & compsub ss′ ss t₁ ⊗ compsub ss′ ss t₂
compsub ss′ ss ⌜zero⌝           = refl
compsub ss′ ss (⌜suc⌝ t)        = ⌜suc⌝ & compsub ss′ ss t
compsub ss′ ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ & compsub ss′ ss tₙ ⊗ compsub ss′ ss t₀
                                    ⊗ ( flip sub tₛ & ( lifts & eqliftsubs ss′ ss ⁻¹
                                                      ⋮ eqliftsubs (lifts ss′) (lifts ss) ⁻¹
                                                      )
                                      ⋮ compsub (lifts (lifts ss′)) (lifts (lifts ss)) tₛ
                                      )

rsk3! = rensubkit3 rsk2! compsub
open RenSubKit3 rsk3! public


----------------------------------------------------------------------------------------------------
