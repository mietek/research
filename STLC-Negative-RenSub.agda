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

compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊑ Γ″) (e : Γ ⊑ Γ′) (t : Γ ⊢ A) →
          ren (e′ ∘⊑ e) t ≡ (ren e′ ∘ ren e) t
compren e′ e (var i)     = var & compren∋ e′ e i
compren e′ e (⌜λ⌝ t)     = ⌜λ⌝ & compren (lift⊑ e′) (lift⊑ e) t
compren e′ e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂
compren e′ e (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂
compren e′ e (⌜fst⌝ t)   = ⌜fst⌝ & compren e′ e t
compren e′ e (⌜snd⌝ t)   = ⌜snd⌝ & compren e′ e t
compren e′ e ⌜unit⌝      = refl

-- not really identity
ridren : ∀ {Γ Γ′ A} (e : Γ ⊑ Γ′) (i : Γ ∋ A) → ren e (var i) ≡ var (ren∋ e i)
ridren e i = refl

-- not really identity
ridsub : ∀ {Γ Ξ A} (ss : Ξ ⊢§ Γ) (i : Γ ∋ A) → sub ss (var i) ≡ sub∋ ss i
ridsub ss i = refl

open RenSubKit1 (kit subkit lidren compren ridren ridsub) public


----------------------------------------------------------------------------------------------------

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊑ Ξ′) (ss : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
           sub (ren§ e ss) t ≡ (ren e ∘ sub ss) t
eqrensub e ss (var i)     = eqrensub∋ e ss i
eqrensub e ss (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftren§ e ss ⁻¹
                                  ⋮ eqrensub (lift⊑ e) (lift§ ss) t
                                  )
eqrensub e ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqrensub e ss t₁ ⊗ eqrensub e ss t₂
eqrensub e ss (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqrensub e ss t₁ ⊗ eqrensub e ss t₂
eqrensub e ss (⌜fst⌝ t)   = ⌜fst⌝ & eqrensub e ss t
eqrensub e ss (⌜snd⌝ t)   = ⌜snd⌝ & eqrensub e ss t
eqrensub e ss ⌜unit⌝      = refl

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢§ Γ′) (e : Γ ⊑ Γ′) (t : Γ ⊢ A) →
           sub (get§ e ss) t ≡ (sub ss ∘ ren e) t
eqsubren ss e (var i)     = eqsubren∋ ss e i
eqsubren ss e (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftget§ e ss ⁻¹
                                  ⋮ eqsubren (lift§ ss) (lift⊑ e) t
                                  )
eqsubren ss e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren ss e t₁ ⊗ eqsubren ss e t₂
eqsubren ss e (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & eqsubren ss e t₁ ⊗ eqsubren ss e t₂
eqsubren ss e (⌜fst⌝ t)   = ⌜fst⌝ & eqsubren ss e t
eqsubren ss e (⌜snd⌝ t)   = ⌜snd⌝ & eqsubren ss e t
eqsubren ss e ⌜unit⌝      = refl

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
compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢§ Ξ) (ss : Ξ ⊢§ Γ) (t : Γ ⊢ A) →
          sub (sub§ ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
compsub ss′ ss (var i)     = compsub∋ ss′ ss i
compsub ss′ ss (⌜λ⌝ t)     = ⌜λ⌝ & ( flip sub t & eqliftsub§ ss′ ss ⁻¹
                                   ⋮ compsub (lift§ ss′) (lift§ ss) t
                                   )
compsub ss′ ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compsub ss′ ss t₁ ⊗ compsub ss′ ss t₂
compsub ss′ ss (t₁ ⌜,⌝ t₂) = _⌜,⌝_ & compsub ss′ ss t₁ ⊗ compsub ss′ ss t₂
compsub ss′ ss (⌜fst⌝ t)   = ⌜fst⌝ & compsub ss′ ss t
compsub ss′ ss (⌜snd⌝ t)   = ⌜snd⌝ & compsub ss′ ss t
compsub ss′ ss ⌜unit⌝      = refl

open RenSubKit3 (kit rensubkit2 compsub) public


----------------------------------------------------------------------------------------------------
