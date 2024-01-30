module STLC-Base-Properties where

open import Common-Properties public
open import STLC-Base


----------------------------------------------------------------------------------------------------

idren⊢ : ∀ {Γ A} (t : Γ ⊢ A) → ren⊢ id⊆ t ≡ t
idren⊢ (⌜v⌝ i)     = ⌜v⌝ & idren∋ i
idren⊢ (⌜λ⌝ t)     = ⌜λ⌝ & idren⊢ t
idren⊢ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & idren⊢ t₁ ⊗ idren⊢ t₂

lidren⊢* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → ren⊢* id⊆ ts ≡ ts
lidren⊢* []       = refl
lidren⊢* (t ∷ ts) = _∷_ & idren⊢ t ⊗ lidren⊢* ts

compren⊢ : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            ren⊢ (e′ ∘⊆ e) t ≡ (ren⊢ e′ ∘ ren⊢ e) t
compren⊢ e′ e (⌜v⌝ i)     = ⌜v⌝ & compren∋ e′ e i
compren⊢ e′ e (⌜λ⌝ t)     = ⌜λ⌝ & compren⊢ (keep e′) (keep e) t
compren⊢ e′ e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren⊢ e′ e t₁ ⊗ compren⊢ e′ e t₂

-- Kovacs: assₛₑₑ
compren⊢* : ∀ {Γ Γ′ Γ″ Δ} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             ren⊢* (e′ ∘⊆ e) ts ≡ (ren⊢* e′ ∘ ren⊢* e) ts
compren⊢* e′ e []       = refl
compren⊢* e′ e (t ∷ ts) = _∷_ & compren⊢ e′ e t ⊗ compren⊢* e′ e ts

eqweakren⊢ : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
              (ren⊢ (keep {A = B} e) ∘ weak⊢) t ≡ (weak⊢ ∘ ren⊢ e) t
eqweakren⊢ e t = compren⊢ (keep e) wk⊆ t ⁻¹
                ⋮ (flip ren⊢ t ∘ drop) & ( rid⊆ e
                                          ⋮ lid⊆ e ⁻¹
                                          )
                ⋮ compren⊢ wk⊆ e t

eqweakren⊢* : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
               (ren⊢* (keep {A = B} e) ∘ weak⊢*) ts ≡ (weak⊢* ∘ ren⊢* e) ts
eqweakren⊢* e []       = refl
eqweakren⊢* e (t ∷ ts) = _∷_ & eqweakren⊢ e t ⊗ eqweakren⊢* e ts

eqliftren⊢* : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
               (ren⊢* (keep {A = B} e) ∘ lift⊢*) ts ≡ (lift⊢* ∘ ren⊢* e) ts
eqliftren⊢* e ts = (⌜v⌝ zero ∷_) & eqweakren⊢* e ts

-- Kovacs: idlₛₑ; not really identity!
ridren⊢* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → ren⊢* e id⊢* ≡ ⊆→⊢* e
ridren⊢* stop     = refl
ridren⊢* (drop e) = (flip ren⊢* id⊢* ∘ drop) & lid⊆ e ⁻¹
                   ⋮ compren⊢* wk⊆ e id⊢*
                   ⋮ weak⊢* & ridren⊢* e
ridren⊢* (keep e) = (⌜v⌝ zero ∷_) & ( eqweakren⊢* e id⊢*
                                     ⋮ weak⊢* & ridren⊢* e
                                     )

module _ (⚠ : Extensionality) where
  ⟪ren⊢⟫ : ∀ (A : Ty) → Presheaf (⟪⊆⟫ ᵒᵖ) ℓzero
  ⟪ren⊢⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = ren⊢
                ; idƒ  = ⚠ idren⊢
                ; _∘ƒ_ = λ e′ e → ⚠ (compren⊢ e′ e)
                }

  ⟪ren⊢*⟫ : ∀ (Δ : Ctx) → Presheaf (⟪⊆⟫ ᵒᵖ) ℓzero
  ⟪ren⊢*⟫ Δ = record
                  { ƒObj = _⊢* Δ
                  ; ƒ    = ren⊢*
                  ; idƒ  = ⚠ lidren⊢*
                  ; _∘ƒ_ = λ e′ e → ⚠ (compren⊢* e′ e)
                  }


----------------------------------------------------------------------------------------------------

-- Kovacs: ∈-ₑ∘ₛ
eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
            sub∋ (get⊢* e ss) i ≡ (sub∋ ss ∘ ren∋ e) i
eqsubren∋ []       stop     i       = refl
eqsubren∋ (s ∷ ss) (drop e) i       = eqsubren∋ ss e i
eqsubren∋ (s ∷ ss) (keep e) zero    = refl
eqsubren∋ (s ∷ ss) (keep e) (suc i) = eqsubren∋ ss e i

-- Kovacs: idlₑₛ
lidget⊢* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → get⊢* id⊆ ts ≡ ts
lidget⊢* []       = refl
lidget⊢* (t ∷ ts) = (t ∷_) & lidget⊢* ts

compget⊢* : ∀ {Γ Δ Δ′ Δ″} (e : Δ ⊆ Δ′) (e′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
             get⊢* (e′ ∘⊆ e) ts ≡ (get⊢* e ∘ get⊢* e′) ts
compget⊢* e        stop      []       = refl
compget⊢* e        (drop e′) (t ∷ ts) = compget⊢* e e′ ts
compget⊢* (drop e) (keep e′) (t ∷ ts) = compget⊢* e e′ ts
compget⊢* (keep e) (keep e′) (t ∷ ts) = (t ∷_) & compget⊢* e e′ ts

-- Kovacs: assₑₛₑ
eqrenget⊢* : ∀ {Γ Γ′ Δ Δ′} (e : Γ ⊆ Γ′) (e′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
              (get⊢* e′ ∘ ren⊢* e) ts ≡ (ren⊢* e ∘ get⊢* e′) ts
eqrenget⊢* e stop      []       = refl
eqrenget⊢* e (drop e′) (t ∷ ts) = eqrenget⊢* e e′ ts
eqrenget⊢* e (keep e′) (t ∷ ts) = (ren⊢ e t ∷_) & eqrenget⊢* e e′ ts

eqliftget⊢* : ∀ {Γ Δ Δ′ B} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
               (get⊢* (keep {A = B} e) ∘ lift⊢*) ts ≡ (lift⊢* ∘ get⊢* e) ts
eqliftget⊢* e ts = (⌜v⌝ zero ∷_) & eqrenget⊢* wk⊆ e ts

-- Kovacs: Tm-ₑ∘ₛ
eqsubren⊢ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
             sub⊢ (get⊢* e ss) t ≡ (sub⊢ ss ∘ ren⊢ e) t
eqsubren⊢ ss e (⌜v⌝ i)     = eqsubren∋ ss e i
eqsubren⊢ ss e (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub⊢ t) & (eqliftget⊢* e ss ⁻¹)
                                    ⋮ eqsubren⊢ (lift⊢* ss) (keep e) t
                                    )
eqsubren⊢ ss e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren⊢ ss e t₁ ⊗ eqsubren⊢ ss e t₂

-- Kovacs: assₛₑₛ
eqsubren⊢* : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
              sub⊢* (get⊢* e ss) ts ≡ (sub⊢* ss ∘ ren⊢* e) ts
eqsubren⊢* ss e []       = refl
eqsubren⊢* ss e (t ∷ ts) = _∷_ & eqsubren⊢ ss e t ⊗ eqsubren⊢* ss e ts

-- Kovacs: idrₑₛ; not really identity!
ridget⊢* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → get⊢* e id⊢* ≡ ⊆→⊢* e
ridget⊢* stop     = refl
ridget⊢* (drop e) = eqrenget⊢* wk⊆ e id⊢*
                   ⋮ weak⊢* & ridget⊢* e
ridget⊢* (keep e) = (⌜v⌝ zero ∷_) & ( eqrenget⊢* wk⊆ e id⊢*
                                     ⋮ weak⊢* & ridget⊢* e
                                     )

module _ (⚠ : Extensionality) where
  ⟪getTms⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ ℓzero
  ⟪getTms⟫ Γ = record
                  { ƒObj = Γ ⊢*_
                  ; ƒ    = get⊢*
                  ; idƒ  = ⚠ lidget⊢*
                  ; _∘ƒ_ = λ e e′ → ⚠ (compget⊢* e e′)
                  }


----------------------------------------------------------------------------------------------------

-- Kovacs: ∈-ₛ∘ₑ
eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
            sub∋ (ren⊢* e ss) i ≡ (ren⊢ e ∘ sub∋ ss) i
eqrensub∋ e (s ∷ ss) zero    = refl
eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

-- Kovacs: ∈-idₛ; not really identity!
idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ id⊢* i ≡ ⌜v⌝ i
idsub∋ zero    = refl
idsub∋ (suc i) = eqrensub∋ wk⊆ id⊢* i
               ⋮ weak⊢ & idsub∋ i
               ⋮ (⌜v⌝ ∘ suc) & idren∋ i

-- Kovacs: ∈-∘ₛ; not really composition!
compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
           sub∋ (sub⊢* ss′ ss) i ≡ (sub⊢ ss′ ∘ sub∋ ss) i
compsub∋ ss′ (s ∷ ss) zero    = refl
compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i

-- Kovacs: Tm-ₛ∘ₑ
eqrensub⊢ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
             sub⊢ (ren⊢* e ss) t ≡ (ren⊢ e ∘ sub⊢ ss) t
eqrensub⊢ e ss (⌜v⌝ i)     = eqrensub∋ e ss i
eqrensub⊢ e ss (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub⊢ t) & eqliftren⊢* e ss ⁻¹
                                    ⋮ eqrensub⊢ (keep e) (lift⊢* ss) t
                                    )
eqrensub⊢ e ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqrensub⊢ e ss t₁ ⊗ eqrensub⊢ e ss t₂

-- Kovacs: assₛₛₑ
eqrensub⊢* : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             sub⊢* (ren⊢* e ss) ts ≡ (ren⊢* e ∘ sub⊢* ss) ts
eqrensub⊢* e ss []       = refl
eqrensub⊢* e ss (t ∷ ts) = _∷_ & eqrensub⊢ e ss t ⊗ eqrensub⊢* e ss ts

-- Kovacs: Tm-idₛ
idsub⊢ : ∀ {Γ A} (t : Γ ⊢ A) → sub⊢ id⊢* t ≡ t
idsub⊢ (⌜v⌝ i)     = idsub∋ i
idsub⊢ (⌜λ⌝ t)     = ⌜λ⌝ & idsub⊢ t
idsub⊢ (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & idsub⊢ t₁ ⊗ idsub⊢ t₂

-- Kovacs: idrₛ
lidsub⊢* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → sub⊢* id⊢* ts ≡ ts
lidsub⊢* []       = refl
lidsub⊢* (t ∷ ts) = _∷_ & idsub⊢ t ⊗ lidsub⊢* ts

eqweaksub⊢ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
              (sub⊢ (lift⊢* {A = B} ss) ∘ weak⊢) t ≡ (weak⊢ ∘ sub⊢ ss) t
eqweaksub⊢ ss t = eqsubren⊢ (lift⊢* ss) wk⊆ t ⁻¹
                 ⋮ (flip sub⊢ t) & ( eqrenget⊢* wk⊆ refl⊆ ss
                                    ⋮ (ren⊢* wk⊆) & lidget⊢* ss
                                    )
                 ⋮ eqrensub⊢ wk⊆ ss t

eqweaksub⊢* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
               (sub⊢* (lift⊢* {A = B} ss) ∘ weak⊢*) ts ≡ (weak⊢* ∘ sub⊢* ss) ts
eqweaksub⊢* ss []       = refl
eqweaksub⊢* ss (t ∷ ts) = _∷_ & eqweaksub⊢ ss t ⊗ eqweaksub⊢* ss ts

eqliftsub⊢* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
               (sub⊢* (lift⊢* {A = B} ss) ∘ lift⊢*) ts ≡ (lift⊢* ∘ sub⊢* ss) ts
eqliftsub⊢* ss ts = (⌜v⌝ zero ∷_) & eqweaksub⊢* ss ts

-- Kovacs: Tm-∘ₛ
compsub⊢ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            sub⊢ (sub⊢* ss′ ss) t ≡ (sub⊢ ss′ ∘ sub⊢ ss) t
compsub⊢ ss′ ss (⌜v⌝ i)     = compsub∋ ss′ ss i
compsub⊢ ss′ ss (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub⊢ t) & eqliftsub⊢* ss′ ss ⁻¹
                                     ⋮ compsub⊢ (lift⊢* ss′) (lift⊢* ss) t
                                     )
compsub⊢ ss′ ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compsub⊢ ss′ ss t₁ ⊗ compsub⊢ ss′ ss t₂

compsub⊢* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             sub⊢* (sub⊢* ss′ ss) ts ≡ (sub⊢* ss′ ∘ sub⊢* ss) ts
compsub⊢* ss′ ss []       = refl
compsub⊢* ss′ ss (t ∷ ts) = _∷_ & compsub⊢ ss′ ss t ⊗ compsub⊢* ss′ ss ts

eqsub⊢ : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          (sub⊢ (s ∷ ss) ∘ weak⊢) t ≡ sub⊢ ss t
eqsub⊢ s ss t = eqsubren⊢ (s ∷ ss) (drop id⊆) t ⁻¹
               ⋮ (flip sub⊢ t) & lidget⊢* ss

eqsub⊢* : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
           (sub⊢* (s ∷ ss) ∘ weak⊢*) ts ≡ sub⊢* ss ts
eqsub⊢* s ss []       = refl
eqsub⊢* s ss (t ∷ ts) = _∷_ & eqsub⊢ s ss t ⊗ eqsub⊢* s ss ts

-- Kovacs: idlₛ
ridsub⊢* : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) → sub⊢* ss id⊢* ≡ ss
ridsub⊢* []       = refl
ridsub⊢* (s ∷ ss) = (s ∷_) & ( eqsub⊢* s ss id⊢*
                              ⋮ ridsub⊢* ss
                              )

-- Kovacs: assₛ
asssub⊢* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
            sub⊢* (sub⊢* ss′ ss) ts ≡ (sub⊢* ss′ ∘ sub⊢* ss) ts
asssub⊢* ss′ ss []       = refl
asssub⊢* ss′ ss (t ∷ ts) = _∷_ & compsub⊢ ss′ ss t ⊗ asssub⊢* ss′ ss ts

⟪⊢*⟫ : Category ℓzero ℓzero
⟪⊢*⟫ = record
          { Obj  = Ctx
          ; _▻_  = _⊢*_
          ; id   = id⊢*
          ; _∘_  = flip sub⊢*
          ; lid▻ = ridsub⊢*
          ; rid▻ = lidsub⊢*
          ; ass▻ = λ ss′ ss ts → asssub⊢* ts ss ss′
          }

module _ (⚠ : Extensionality) where
  ⟪sub⊢⟫ : ∀ (A : Ty) → Presheaf ⟪⊢*⟫ ℓzero
  ⟪sub⊢⟫ A = record
                { ƒObj = _⊢ A
                ; ƒ    = sub⊢
                ; idƒ  = ⚠ idsub⊢
                ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub⊢ ss′ ss)
                }


----------------------------------------------------------------------------------------------------
