module STLC-Base-Properties where

open import Common-Properties public
open import STLC-Base public


----------------------------------------------------------------------------------------------------

idren : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t
idren (⌜v⌝ i)     = ⌜v⌝ & idren∋ i
idren (⌜λ⌝ t)     = ⌜λ⌝ & idren t
idren (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & idren t₁ ⊗ idren t₂

lidrens : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → rens id⊆ ts ≡ ts
lidrens []       = refl
lidrens (t ∷ ts) = _∷_ & idren t ⊗ lidrens ts

compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
          ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t
compren e′ e (⌜v⌝ i)     = ⌜v⌝ & compren∋ e′ e i
compren e′ e (⌜λ⌝ t)     = ⌜λ⌝ & compren (keep e′) (keep e) t
compren e′ e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compren e′ e t₁ ⊗ compren e′ e t₂

-- Kovacs: assₛₑₑ
comprens : ∀ {Γ Γ′ Γ″ Δ} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
           rens (e′ ∘⊆ e) ts ≡ (rens e′ ∘ rens e) ts
comprens e′ e []       = refl
comprens e′ e (t ∷ ts) = _∷_ & compren e′ e t ⊗ comprens e′ e ts

eqweakren : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
            (ren (keep {A = B} e) ∘ weak) t ≡ (weak ∘ ren e) t
eqweakren e t = compren (keep e) wk⊆ t ⁻¹
              ⋮ (flip ren t ∘ drop) & ( rid⊆ e
                                      ⋮ lid⊆ e ⁻¹
                                      )
              ⋮ compren wk⊆ e t

eqweakrens : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             (rens (keep {A = B} e) ∘ weaks) ts ≡ (weaks ∘ rens e) ts
eqweakrens e []       = refl
eqweakrens e (t ∷ ts) = _∷_ & eqweakren e t ⊗ eqweakrens e ts

eqliftrens : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
             (rens (keep {A = B} e) ∘ lifts) ts ≡ (lifts ∘ rens e) ts
eqliftrens e ts = (⌜v⌝ zero ∷_) & eqweakrens e ts

-- Kovacs: idlₛₑ; not really identity!
ridrens : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → rens e ids ≡ vars e
ridrens stop     = refl
ridrens (drop e) = (flip rens ids ∘ drop) & lid⊆ e ⁻¹
                 ⋮ comprens wk⊆ e ids
                 ⋮ weaks & ridrens e
ridrens (keep e) = (⌜v⌝ zero ∷_) & ( eqweakrens e ids
                                   ⋮ weaks & ridrens e
                                   )

module _ (⚠ : Extensionality) where
  ⟪ren⟫ : ∀ (A : Ty) → Presheaf (⟪⊆⟫ ᵒᵖ) ℓzero
  ⟪ren⟫ A = record
              { ƒObj = _⊢ A
              ; ƒ    = ren
              ; idƒ  = ⚠ idren
              ; _∘ƒ_ = λ e′ e → ⚠ (compren e′ e)
              }

  ⟪rens⟫ : ∀ (Δ : Ctx) → Presheaf (⟪⊆⟫ ᵒᵖ) ℓzero
  ⟪rens⟫ Δ = record
               { ƒObj = _⊢* Δ
               ; ƒ    = rens
               ; idƒ  = ⚠ lidrens
               ; _∘ƒ_ = λ e′ e → ⚠ (comprens e′ e)
               }


----------------------------------------------------------------------------------------------------

-- Kovacs: ∈-ₑ∘ₛ
eqsubren∋ : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
            sub∋ (gets e ss) i ≡ (sub∋ ss ∘ ren∋ e) i
eqsubren∋ []       stop     i       = refl
eqsubren∋ (s ∷ ss) (drop e) i       = eqsubren∋ ss e i
eqsubren∋ (s ∷ ss) (keep e) zero    = refl
eqsubren∋ (s ∷ ss) (keep e) (suc i) = eqsubren∋ ss e i

-- Kovacs: idlₑₛ
lidgets : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → gets id⊆ ts ≡ ts
lidgets []       = refl
lidgets (t ∷ ts) = (t ∷_) & lidgets ts

compgets : ∀ {Γ Δ Δ′ Δ″} (e : Δ ⊆ Δ′) (e′ : Δ′ ⊆ Δ″) (ts : Γ ⊢* Δ″) →
           gets (e′ ∘⊆ e) ts ≡ (gets e ∘ gets e′) ts
compgets e        stop      []       = refl
compgets e        (drop e′) (t ∷ ts) = compgets e e′ ts
compgets (drop e) (keep e′) (t ∷ ts) = compgets e e′ ts
compgets (keep e) (keep e′) (t ∷ ts) = (t ∷_) & compgets e e′ ts

-- Kovacs: assₑₛₑ
eqrengets : ∀ {Γ Γ′ Δ Δ′} (e : Γ ⊆ Γ′) (e′ : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
            (gets e′ ∘ rens e) ts ≡ (rens e ∘ gets e′) ts
eqrengets e stop      []       = refl
eqrengets e (drop e′) (t ∷ ts) = eqrengets e e′ ts
eqrengets e (keep e′) (t ∷ ts) = (ren e t ∷_) & eqrengets e e′ ts

eqliftgets : ∀ {Γ Δ Δ′ B} (e : Δ ⊆ Δ′) (ts : Γ ⊢* Δ′) →
             (gets (keep {A = B} e) ∘ lifts) ts ≡ (lifts ∘ gets e) ts
eqliftgets e ts = (⌜v⌝ zero ∷_) & eqrengets wk⊆ e ts

-- Kovacs: Tm-ₑ∘ₛ
eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
           sub (gets e ss) t ≡ (sub ss ∘ ren e) t
eqsubren ss e (⌜v⌝ i)     = eqsubren∋ ss e i
eqsubren ss e (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub t) & (eqliftgets e ss ⁻¹)
                                  ⋮ eqsubren (lifts ss) (keep e) t
                                  )
eqsubren ss e (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqsubren ss e t₁ ⊗ eqsubren ss e t₂

-- Kovacs: assₛₑₛ
eqsubrens : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
            subs (gets e ss) ts ≡ (subs ss ∘ rens e) ts
eqsubrens ss e []       = refl
eqsubrens ss e (t ∷ ts) = _∷_ & eqsubren ss e t ⊗ eqsubrens ss e ts

-- Kovacs: idrₑₛ; not really identity!
ridgets : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → gets e ids ≡ vars e
ridgets stop     = refl
ridgets (drop e) = eqrengets wk⊆ e ids
                 ⋮ weaks & ridgets e
ridgets (keep e) = (⌜v⌝ zero ∷_) & ( eqrengets wk⊆ e ids
                                   ⋮ weaks & ridgets e
                                   )

module _ (⚠ : Extensionality) where
  ⟪getTms⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ ℓzero
  ⟪getTms⟫ Γ = record
                 { ƒObj = Γ ⊢*_
                 ; ƒ    = gets
                 ; idƒ  = ⚠ lidgets
                 ; _∘ƒ_ = λ e e′ → ⚠ (compgets e e′)
                 }


----------------------------------------------------------------------------------------------------

-- Kovacs: ∈-ₛ∘ₑ
eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
            sub∋ (rens e ss) i ≡ (ren e ∘ sub∋ ss) i
eqrensub∋ e (s ∷ ss) zero    = refl
eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

-- Kovacs: ∈-idₛ; not really identity!
idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ ids i ≡ ⌜v⌝ i
idsub∋ zero    = refl
idsub∋ (suc i) = eqrensub∋ wk⊆ ids i
               ⋮ weak & idsub∋ i
               ⋮ (⌜v⌝ ∘ suc) & idren∋ i

-- Kovacs: ∈-∘ₛ; not really composition!
compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
           sub∋ (subs ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
compsub∋ ss′ (s ∷ ss) zero    = refl
compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i

-- Kovacs: Tm-ₛ∘ₑ
eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
           sub (rens e ss) t ≡ (ren e ∘ sub ss) t
eqrensub e ss (⌜v⌝ i)     = eqrensub∋ e ss i
eqrensub e ss (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub t) & eqliftrens e ss ⁻¹
                                  ⋮ eqrensub (keep e) (lifts ss) t
                                  )
eqrensub e ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & eqrensub e ss t₁ ⊗ eqrensub e ss t₂

-- Kovacs: assₛₛₑ
eqrensubs : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
            subs (rens e ss) ts ≡ (rens e ∘ subs ss) ts
eqrensubs e ss []       = refl
eqrensubs e ss (t ∷ ts) = _∷_ & eqrensub e ss t ⊗ eqrensubs e ss ts

-- Kovacs: Tm-idₛ
idsub : ∀ {Γ A} (t : Γ ⊢ A) → sub ids t ≡ t
idsub (⌜v⌝ i)     = idsub∋ i
idsub (⌜λ⌝ t)     = ⌜λ⌝ & idsub t
idsub (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & idsub t₁ ⊗ idsub t₂

-- Kovacs: idrₛ
lidsubs : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → subs ids ts ≡ ts
lidsubs []       = refl
lidsubs (t ∷ ts) = _∷_ & idsub t ⊗ lidsubs ts

eqweaksub : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
            (sub (lifts {A = B} ss) ∘ weak) t ≡ (weak ∘ sub ss) t
eqweaksub ss t = eqsubren (lifts ss) wk⊆ t ⁻¹
               ⋮ (flip sub t) & ( eqrengets wk⊆ id⊆ ss
                                ⋮ (rens wk⊆) & lidgets ss
                                )
               ⋮ eqrensub wk⊆ ss t

eqweaksubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             (subs (lifts {A = B} ss) ∘ weaks) ts ≡ (weaks ∘ subs ss) ts
eqweaksubs ss []       = refl
eqweaksubs ss (t ∷ ts) = _∷_ & eqweaksub ss t ⊗ eqweaksubs ss ts

eqliftsubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
             (subs (lifts {A = B} ss) ∘ lifts) ts ≡ (lifts ∘ subs ss) ts
eqliftsubs ss ts = (⌜v⌝ zero ∷_) & eqweaksubs ss ts

-- Kovacs: Tm-∘ₛ
compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
          sub (subs ss′ ss) t ≡ (sub ss′ ∘ sub ss) t
compsub ss′ ss (⌜v⌝ i)     = compsub∋ ss′ ss i
compsub ss′ ss (⌜λ⌝ t)     = ⌜λ⌝ & ( (flip sub t) & eqliftsubs ss′ ss ⁻¹
                                   ⋮ compsub (lifts ss′) (lifts ss) t
                                   )
compsub ss′ ss (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & compsub ss′ ss t₁ ⊗ compsub ss′ ss t₂

compsubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
           subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
compsubs ss′ ss []       = refl
compsubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ compsubs ss′ ss ts

eqsub : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
        (sub (s ∷ ss) ∘ weak) t ≡ sub ss t
eqsub s ss t = eqsubren (s ∷ ss) (drop id⊆) t ⁻¹
             ⋮ (flip sub t) & lidgets ss

eqsubs : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
         (subs (s ∷ ss) ∘ weaks) ts ≡ subs ss ts
eqsubs s ss []       = refl
eqsubs s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsubs s ss ts

-- Kovacs: idlₛ
ridsubs : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) → subs ss ids ≡ ss
ridsubs []       = refl
ridsubs (s ∷ ss) = (s ∷_) & ( eqsubs s ss ids
                            ⋮ ridsubs ss
                            )

-- Kovacs: assₛ
asssubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
          subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
asssubs ss′ ss []       = refl
asssubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ asssubs ss′ ss ts

⟪⊢*⟫ : Category ℓzero ℓzero
⟪⊢*⟫ = record
          { Obj  = Ctx
          ; _▻_  = _⊢*_
          ; id   = ids
          ; _∘_  = flip subs
          ; lid▻ = ridsubs
          ; rid▻ = lidsubs
          ; ass▻ = λ ss′ ss ts → asssubs ts ss ss′
          }

module _ (⚠ : Extensionality) where
  ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪⊢*⟫ ℓzero
  ⟪sub⟫ A = record
              { ƒObj = _⊢ A
              ; ƒ    = sub
              ; idƒ  = ⚠ idsub
              ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
              }


----------------------------------------------------------------------------------------------------

-- stability under renaming
module _ where
  open ≡-Reasoning

  renβred⊃ : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
             (_[ ren e t₂ ] ∘ ren (keep e)) t₁ ≡ (ren e ∘ _[ t₂ ]) t₁
  renβred⊃ e t₁ t₂ =
      begin
        (sub (ren e t₂ ∷ ids) ∘ ren (keep e)) t₁
      ≡⟨ eqsubren (ren e t₂ ∷ ids) (keep e) t₁ ⁻¹ ⟩
        sub (gets (keep e) (ren e t₂ ∷ ids)) t₁
      ≡⟨ (flip sub t₁ ∘ (ren e t₂ ∷_)) & (
          begin
            gets e ids
          ≡⟨ ridgets e ⟩
            vars e
          ≡⟨ ridrens e ⁻¹ ⟩
            rens e ids
          ∎) ⟩
        sub (ren e t₂ ∷ rens e ids) t₁
      ≡⟨ eqrensub e (t₂ ∷ ids) t₁ ⟩
        (ren e ∘ sub (t₂ ∷ ids)) t₁
      ∎


----------------------------------------------------------------------------------------------------

-- stability under substitution
module _ where
  open ≡-Reasoning

  subβred⊃ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
             (_[ sub ss t₂ ] ∘ sub (lifts ss)) t₁ ≡ (sub ss ∘ _[ t₂ ]) t₁
  subβred⊃ ss t₁ t₂ =
      begin
        (sub (sub ss t₂ ∷ ids) ∘ sub (lifts ss)) t₁
      ≡˘⟨ compsub (sub ss t₂ ∷ ids) (lifts ss) t₁ ⟩
        sub (subs (sub ss t₂ ∷ ids) (lifts ss)) t₁
      ≡⟨ (flip sub t₁ ∘ (sub ss t₂ ∷_)) & (
          begin
            (subs (sub ss t₂ ∷ ids) ∘ weaks) ss
          ≡˘⟨ eqsubrens (sub ss t₂ ∷ ids) (drop id⊆) ss ⟩
            subs (gets (drop id⊆) (sub ss t₂ ∷ ids)) ss
          ≡⟨⟩
            subs (gets id⊆ ids) ss
          ≡⟨ flip subs ss & lidgets ids ⟩
            subs ids ss
          ≡⟨ lidsubs ss ⟩
            ss
          ≡˘⟨ ridsubs ss ⟩
            subs ss ids
          ∎) ⟩
        sub (subs ss (t₂ ∷ ids)) t₁
      ≡⟨ compsub ss (t₂ ∷ ids) t₁ ⟩
        (sub ss ∘ sub (t₂ ∷ ids)) t₁
      ∎


----------------------------------------------------------------------------------------------------
