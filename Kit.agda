module Kit where

open import Common-Properties public


----------------------------------------------------------------------------------------------------

module CtxKit (Ty : Set) where
  Ctx : Set
  Ctx = List Ty


----------------------------------------------------------------------------------------------------

  module ⊢*Kit
    (Tm : Ctx → Ty → Set)
      where
    private
      infix 3 _⊢_
      _⊢_ = Tm

    ty : ∀ {Γ A} → Γ ⊢ A → Ty
    ty {A = A} t = A

    -- simultaneous substitutions
    infix 3 _⊢*_
    data _⊢*_ (Γ : Ctx) : Ctx → Set where
      []  : Γ ⊢* []
      _∷_ : ∀ {A Δ} (t : Γ ⊢ A) (ts : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ

    -- TODO: consider using Data.List.Relation.Unary.All
    -- _⊢*_ : Ctx → Ctx → Set
    -- Γ ⊢* Δ = All (Γ ⊢_) Δ


----------------------------------------------------------------------------------------------------

    module RenKit
      (⌜v⌝ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A)
      (ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A)
        where
      weak : ∀ {Γ A B} → Γ ⊢ B → A ∷ Γ ⊢ B
      weak t = ren wk⊆ t

      -- Kovacs: flip _ₛ∘ₑ_
      rens : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
      rens e []       = []
      rens e (t ∷ ts) = ren e t ∷ rens e ts

      weaks : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* Δ
      weaks ts = rens wk⊆ ts

      lifts : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* A ∷ Δ
      lifts ts = ⌜v⌝ zero ∷ weaks ts

      -- Kovacs: ⌜_⌝ᵒᵖᵉ
      vars : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ′ ⊢* Γ
      vars stop     = []
      vars (drop e) = weaks (vars e)
      vars (keep e) = lifts (vars e)

      -- TODO: check if varying this affects anything
      ids : ∀ {Γ} → Γ ⊢* Γ
      ids {[]}    = []
      ids {A ∷ Γ} = lifts ids
      -- ids = vars id⊆

      refls : ∀ {Γ} → Γ ⊢* Γ
      refls = ids

      -- substitution of indices
      sub∋ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ∋ A → Ξ ⊢ A
      sub∋ (s ∷ ss) zero    = s
      sub∋ (s ∷ ss) (suc i) = sub∋ ss i


----------------------------------------------------------------------------------------------------

      module RenPropertiesKit
        (lidren  : ∀ {Γ A} (t : Γ ⊢ A) → ren id⊆ t ≡ t)
        (ridren  : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (⌜v⌝ i) ≡ ⌜v⌝ (ren∋ e i))
        (compren : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
                   ren (e′ ∘⊆ e) t ≡ (ren e′ ∘ ren e) t)
          where

        lidrens : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → rens id⊆ ts ≡ ts
        lidrens []       = refl
        lidrens (t ∷ ts) = _∷_ & lidren t ⊗ lidrens ts

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

        open ≡-Reasoning

        eqliftrens : ∀ {Γ Γ′ Δ B} (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
                     (rens (keep {A = B} e) ∘ lifts) ts ≡ (lifts ∘ rens e) ts
        eqliftrens e ts = (_∷ (rens (keep e) ∘ weaks) ts) & ridren (keep e) zero
                        ⋮ (⌜v⌝ zero ∷_) & eqweakrens e ts

        -- Kovacs: idlₛₑ; not really identity
        ridrens : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → rens e ids ≡ vars e
        ridrens stop     = refl
        ridrens (drop e) = (flip rens ids ∘ drop) & lid⊆ e ⁻¹
                         ⋮ comprens wk⊆ e ids
                         ⋮ weaks & ridrens e
        ridrens (keep e) = (_∷ (rens (keep e) ∘ weaks) ids) & ridren (keep e) zero
                         ⋮ (⌜v⌝ zero ∷_) & ( eqweakrens e ids
                                           ⋮ weaks & ridrens e
                                           )

        module _ (⚠ : Extensionality) where
          ⟪ren⟫ : ∀ (A : Ty) → Presheaf (⟪⊆⟫ ᵒᵖ) ℓzero
          ⟪ren⟫ A = record
                      { ƒObj = _⊢ A
                      ; ƒ    = ren
                      ; idƒ  = ⚠ lidren
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

      module SubKit
        (sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A)
          where
        -- Kovacs: flip _∘ₛ_
        subs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
        subs ss []       = []
        subs ss (t ∷ ts) = sub ss t ∷ subs ss ts

        transs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
        transs = subs

        _∘s_ : ∀ {Γ Ξ Δ} → Γ ⊢* Δ → Ξ ⊢* Γ → Ξ ⊢* Δ
        _∘s_ = flip transs

        _[_] : ∀ {Γ A B} → A ∷ Γ ⊢ B → Γ ⊢ A → Γ ⊢ B
        t [ s ] = sub (s ∷ ids) t

        _[_∣_] : ∀ {Γ A B C} → B ∷ A ∷ Γ ⊢ C → Γ ⊢ A → Γ ⊢ B → Γ ⊢ C
        t [ s₁ ∣ s₂ ] = sub (s₂ ∷ s₁ ∷ ids) t

        -- Kovacs: _ₑ∘ₛ_; flip?
        gets : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
        gets stop     ts       = ts
        gets (drop e) (t ∷ ts) = gets e ts
        gets (keep e) (t ∷ ts) = t ∷ gets e ts


----------------------------------------------------------------------------------------------------

        -- TODO: clean this up
        module SubPropertiesKit1
          (ridren  : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → ren e (⌜v⌝ i) ≡ ⌜v⌝ (ren∋ e i))
          (ridrens : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → rens e ids ≡ vars e)
            where
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

          -- Kovacs: idrₑₛ; not really identity
          ridgets : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → gets e ids ≡ vars e
          ridgets stop     = refl
          ridgets (drop e) = eqrengets wk⊆ e ids
                           ⋮ weaks & ridgets e
          ridgets (keep e) = (⌜v⌝ zero ∷_) & ( eqrengets wk⊆ e ids
                                             ⋮ weaks & ridgets e
                                             )

          module _ (⚠ : Extensionality) where
            ⟪gets⟫ : ∀ (Γ : Ctx) → Presheaf ⟪⊆⟫ ℓzero
            ⟪gets⟫ Γ = record
                         { ƒObj = Γ ⊢*_
                         ; ƒ    = gets
                         ; idƒ  = ⚠ lidgets
                         ; _∘ƒ_ = λ e e′ → ⚠ (compgets e e′)
                         }

          -- Kovacs: ∈-ₛ∘ₑa
          eqrensub∋ : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
                      sub∋ (rens e ss) i ≡ (ren e ∘ sub∋ ss) i
          eqrensub∋ e (s ∷ ss) zero    = refl
          eqrensub∋ e (s ∷ ss) (suc i) = eqrensub∋ e ss i

          -- Kovacs: ∈-idₛ; not really identity
          idsub∋ : ∀ {Γ A} (i : Γ ∋ A) → sub∋ ids i ≡ ⌜v⌝ i
          idsub∋ zero    = refl
          idsub∋ (suc i) = eqrensub∋ wk⊆ ids i
                         ⋮ weak & idsub∋ i
                         ⋮ ridren wk⊆ i
                         ⋮ (⌜v⌝ ∘ suc) & idren∋ i

          -- Kovacs: ∈-∘ₛ; not really composition
          compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
                     sub∋ (subs ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
          compsub∋ ss′ (s ∷ ss) zero    = refl
          compsub∋ ss′ (s ∷ ss) (suc i) = compsub∋ ss′ ss i

          module SubPropertiesKit2
            (eqsubren : ∀ {Γ Γ′ Ξ A} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (t : Γ ⊢ A) →
                        sub (gets e ss) t ≡ (sub ss ∘ ren e) t)
            (eqrensub : ∀ {Γ Ξ Ξ′ A} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
                        sub (rens e ss) t ≡ (ren e ∘ sub ss) t)
            (lidsub   : ∀ {Γ A} (t : Γ ⊢ A) → sub ids t ≡ t)
            (ridsub   : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → sub ss (⌜v⌝ i) ≡ sub∋ ss i)
              where            -- Kovacs: assₛₑₛ
            eqsubrens : ∀ {Γ Γ′ Ξ Δ} (ss : Ξ ⊢* Γ′) (e : Γ ⊆ Γ′) (ts : Γ ⊢* Δ) →
                        subs (gets e ss) ts ≡ (subs ss ∘ rens e) ts
            eqsubrens ss e []       = refl
            eqsubrens ss e (t ∷ ts) = _∷_ & eqsubren ss e t ⊗ eqsubrens ss e ts

            -- Kovacs: assₛₛₑ
            eqrensubs : ∀ {Γ Ξ Ξ′ Δ} (e : Ξ ⊆ Ξ′) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                        subs (rens e ss) ts ≡ (rens e ∘ subs ss) ts
            eqrensubs e ss []       = refl
            eqrensubs e ss (t ∷ ts) = _∷_ & eqrensub e ss t ⊗ eqrensubs e ss ts

            -- Kovacs: idrₛ
            lidsubs : ∀ {Γ Δ} (ts : Γ ⊢* Δ) → subs ids ts ≡ ts
            lidsubs []       = refl
            lidsubs (t ∷ ts) = _∷_ & lidsub t ⊗ lidsubs ts

            eqweaksub : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
                        (sub (lifts {A = B} ss) ∘ weak) t ≡ (weak ∘ sub ss) t
            eqweaksub ss t = eqsubren (lifts ss) wk⊆ t ⁻¹
                           ⋮ flip sub t & ( eqrengets wk⊆ id⊆ ss
                                          ⋮ (rens wk⊆) & lidgets ss
                                          )
                           ⋮ eqrensub wk⊆ ss t

            eqweaksubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                         (subs (lifts {A = B} ss) ∘ weaks) ts ≡ (weaks ∘ subs ss) ts
            eqweaksubs ss []       = refl
            eqweaksubs ss (t ∷ ts) = _∷_ & eqweaksub ss t ⊗ eqweaksubs ss ts

            eqliftsubs : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                         (subs (lifts {A = B} ss) ∘ lifts) ts ≡ (lifts ∘ subs ss) ts
            eqliftsubs ss ts = (_∷ (subs (lifts ss) ∘ weaks) ts) & ridsub (lifts ss) zero
                             ⋮ (⌜v⌝ zero ∷_) & eqweaksubs ss ts

            -- TODO: clean this up
            module SubPropertiesKit3
              (compsub : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
                         sub (subs ss′ ss) t ≡ (sub ss′ ∘ sub ss) t)
                where
              compsubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                         subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
              compsubs ss′ ss []       = refl
              compsubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ compsubs ss′ ss ts

              eqsub : ∀ {Γ Ξ A B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (t : Γ ⊢ A) →
                      (sub (s ∷ ss) ∘ weak) t ≡ sub ss t
              eqsub s ss t = eqsubren (s ∷ ss) (drop id⊆) t ⁻¹
                           ⋮ flip sub t & lidgets ss

              eqsubs : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                       (subs (s ∷ ss) ∘ weaks) ts ≡ subs ss ts
              eqsubs s ss []       = refl
              eqsubs s ss (t ∷ ts) = _∷_ & eqsub s ss t ⊗ eqsubs s ss ts

              -- Kovacs: idlₛ
              ridsubs : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) → subs ss ids ≡ ss
              ridsubs []       = refl
              ridsubs (s ∷ ss) = (_∷ (subs (s ∷ ss) ∘ weaks) ids) & ridsub (s ∷ ss) zero
                               ⋮ (s ∷_) & ( eqsubs s ss ids
                                          ⋮ ridsubs ss
                                          )

              -- Kovacs: assₛ
              asssubs : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
                        subs (subs ss′ ss) ts ≡ (subs ss′ ∘ subs ss) ts
              asssubs ss′ ss []       = refl
              asssubs ss′ ss (t ∷ ts) = _∷_ & compsub ss′ ss t ⊗ asssubs ss′ ss ts

              ⟪subs⟫ : Category ℓzero ℓzero
              ⟪subs⟫ = record
                         { Obj  = Ctx
                         ; _▻_  = _⊢*_
                         ; id   = ids
                         ; _∘_  = flip subs
                         ; lid▻ = ridsubs
                         ; rid▻ = lidsubs
                         ; ass▻ = λ ss′ ss ts → asssubs ts ss ss′
                         }

              module _ (⚠ : Extensionality) where
                ⟪sub⟫ : ∀ (A : Ty) → Presheaf ⟪subs⟫ ℓzero
                ⟪sub⟫ A = record
                            { ƒObj = _⊢ A
                            ; ƒ    = sub
                            ; idƒ  = ⚠ lidsub
                            ; _∘ƒ_ = λ ss′ ss → ⚠ (compsub ss′ ss)
                            }

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

                subβred⊃ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
                           (_[ sub ss t₂ ] ∘ sub (lifts ss)) t₁ ≡ (sub ss ∘ _[ t₂ ]) t₁
                subβred⊃ ss t₁ t₂ =
                    begin
                      (sub (sub ss t₂ ∷ ids) ∘ sub (lifts ss)) t₁
                    ≡˘⟨ compsub (sub ss t₂ ∷ ids) (lifts ss) t₁ ⟩
                      sub (subs (sub ss t₂ ∷ ids) (lifts ss)) t₁
                    ≡⟨ flip sub t₁ & ((_∷ (subs (sub ss t₂ ∷ ids) ∘ weaks) ss) & ridsub (sub ss t₂ ∷ ids) zero) ⟩
                      sub (sub ss t₂ ∷ subs (sub ss t₂ ∷ ids) (weaks ss)) t₁
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

    module NFKit
      (NF  : ∀ {Γ A} → Γ ⊢ A → Set)
      (NNF : ∀ {Γ A} → Γ ⊢ A → Set)
        where
      data NF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
        []  : NF* []
        _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NF t → NF* ts → NF* (t ∷ ts)

      data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
        []  : NNF* []
        _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)


----------------------------------------------------------------------------------------------------

    module ≝Kit
      {_≝_    : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set}
      (refl≝  : ∀ {Γ A} {t : Γ ⊢ A} → t ≝ t)
      (sym≝   : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t)
      (trans≝ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t″ → t ≝ t″)
        where
      ≡→≝ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≝ t′
      ≡→≝ refl = refl≝

      module ≝-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t ≝ t′
        begin_ deq = deq

        infixr 2 _≝⟨_⟩_
        _≝⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≝ t′ → t′ ≝ t″ → t ≝ t″
        t ≝⟨ deq ⟩ deq′ = trans≝ deq deq′

        infixr 2 _≝˘⟨_⟩_
        _≝˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≝ t → t′ ≝ t″ → t ≝ t″
        t ≝˘⟨ deq ⟩ deq′ = trans≝ (sym≝ deq) deq′

        infixr 2 _≡⟨⟩_
        _≡⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ≝ t′ → t ≝ t′
        t ≡⟨⟩ deq = deq

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ≝ t″ → t ≝ t″
        t ≡⟨ eq ⟩ deq′ = trans≝ (≡→≝ eq) deq′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ≝ t″ → t ≝ t″
        t ≡˘⟨ eq ⟩ deq′ = trans≝ (≡→≝ (sym eq)) deq′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ t
        t ∎ = refl≝


----------------------------------------------------------------------------------------------------

    module ⇒Kit
      (Red : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set)
        where
      private
        infix 4 _⇒_
        _⇒_ = Red

      -- reducible forms
      RF : ∀ {Γ A} → Γ ⊢ A → Set
      RF t = Σ _ λ t′ → t ⇒ t′

      -- irreducible forms
      ¬R : ∀ {Γ A} → Γ ⊢ A → Set
      ¬R t = ∀ {t′} → ¬ t ⇒ t′

      -- iterated reduction
      infix 4 _⇒*_
      data _⇒*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
        done : ∀ {t} → t ⇒* t
        step : ∀ {t t′ t″} (r : t ⇒ t′) (rs : t′ ⇒* t″) → t ⇒* t″

      trans⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
      trans⇒* done        rs′ = rs′
      trans⇒* (step r rs) rs′ = step r (trans⇒* rs rs′)

      ≡→⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ⇒* t′
      ≡→⇒* refl = done

      module ⇒-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → t ⇒* t′
        begin_ rs = rs

        infixr 2 _⇒*⟨_⟩_
        _⇒*⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒*⟨ rs ⟩ rs′ = trans⇒* rs rs′

        infixr 2 _⇒⟨_⟩_
        _⇒⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒ t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒⟨ r ⟩ rs = step r rs

        infixr 2 _≡⟨⟩_
        _≡⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ⇒* t′ → t ⇒* t′
        t ≡⟨⟩ rs = rs

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ⇒* t″ → t ⇒* t″
        t ≡⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* eq) rs′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ⇒* t″ → t ⇒* t″
        t ≡˘⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* (sym eq)) rs′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ⇒* t
        t ∎ = done

      module _ (⚠ : Extensionality) where
        uni¬RF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ RF t) → ¬p ≡ ¬p′
        uni¬RF = uni→ ⚠ uni𝟘


----------------------------------------------------------------------------------------------------

      module ¬RKit
        {NF      : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R  : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
          where
        ¬RF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → ¬R t
        ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

        ¬R→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → ¬ RF t
        ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

        RF→¬NF : ∀ {Γ A} {t : Γ ⊢ A} → RF t → ¬ NF t
        RF→¬NF (_ , r) p = r ↯ NF→¬R p

        NF→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬ RF t
        NF→¬RF = ¬R→¬RF ∘ NF→¬R

        -- progress
        data Prog {Γ A} (t : Γ ⊢ A) : Set where
          done : NF t → Prog t
          step : ∀ {t′ : Γ ⊢ A} → t ⇒ t′ → Prog t

        -- NOTE: the above is slightly more convenient than the equivalent below
        -- step : Σ (Γ ⊢ A) (λ t′ → t ⇒ t′) → Prog t

        recProg : ∀ {𝓍} {X : Set 𝓍} {Γ A} {t : Γ ⊢ A} → Prog t → (NF t → X) → (RF t → X) → X
        recProg (done p) f₁ f₂ = f₁ p
        recProg (step r) f₁ f₂ = f₂ (_ , r)


----------------------------------------------------------------------------------------------------

        module ProgKit
          (prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t)
            where
          NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
          NF? t = recProg (prog⇒ t) yes (no ∘ RF→¬NF)

          RF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
          RF? t = recProg (prog⇒ t) (no ∘ NF→¬RF) yes

          ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
          ¬NF→RF ¬p = recProg (prog⇒ _) (_↯ ¬p) id

          ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
          ¬RF→NF ¬p = recProg (prog⇒ _) id (_↯ ¬p)

          ¬R→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → NF t
          ¬R→NF = ¬RF→NF ∘ ¬R→¬RF

        module NF?Kit
          (NF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t))
          (¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t)
            where
          prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
          prog⇒ t    with NF? t
          ... | yes p   = done p
          ... | no ¬p   = let _ , r = ¬NF→RF ¬p
                            in step r

          open ProgKit prog⇒ public hiding (NF? ; ¬NF→RF)

        module RF?Kit
          (RF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t))
          (¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t)
            where
          prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
          prog⇒ t          with RF? t
          ... | yes (_ , r)   = step r
          ... | no ¬p         = done (¬RF→NF ¬p)

          open ProgKit prog⇒ public hiding (RF? ; ¬RF→NF)


----------------------------------------------------------------------------------------------------

      module ⇒*Kit
        {NF     : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
        (det⇒  : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″)
        (uni⇒  : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′)
          where
        skip⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒* t″ → NF t″ → t′ ⇒* t″
        skip⇒* r done          p″ = r ↯ NF→¬R p″
        skip⇒* r (step r′ rs′) p″ with det⇒ r r′
        ... | refl                  = rs′

        -- determinism
        det⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → NF t′ → t ⇒* t″ → NF t″ → t′ ≡ t″
        det⇒* done        p′ done          p″ = refl
        det⇒* done        p′ (step r′ rs′) p″ = r′ ↯ NF→¬R p′
        det⇒* (step r rs) p′ rs′           p″ = det⇒* rs p′ (skip⇒* r rs′ p″) p″

        -- uniqueness of proofs
        uni⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} (rs rs′ : t ⇒* t′) → NF t′ → rs ≡ rs′
        uni⇒* done        done          p′ = refl
        uni⇒* done        (step r′ rs′) p′ = r′ ↯ NF→¬R p′
        uni⇒* (step r rs) done          p′ = r ↯ NF→¬R p′
        uni⇒* (step r rs) (step r′ rs′) p′ with det⇒ r r′
        ... | refl                            = step & uni⇒ r r′ ⊗ uni⇒* rs rs′ p′

        -- local confluence
        lconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒ t₁ → t ⇒ t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        lconf⇒ r r′ with det⇒ r r′
        ... | refl     = _ , done , done

        -- global confluence
        gconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒* t₁ → t ⇒* t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        gconf⇒ done        rs′           = _ , rs′ , done
        gconf⇒ (step r rs) done          = _ , done , step r rs
        gconf⇒ (step r rs) (step r′ rs′) with det⇒ r r′
        ... | refl                          = gconf⇒ rs rs′


----------------------------------------------------------------------------------------------------

  module ⊩Kit
    (_⊩_ : Ctx → Ty → Set)
    (vren : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A)
      where
    -- semantic environments
    infix 3 _⊩*_
    data _⊩*_ (W : Ctx) : Ctx → Set where
      []  : W ⊩* []
      _∷_ : ∀ {Δ A} (v : W ⊩ A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

    vrens : ∀ {W W′ Δ} → W ⊆ W′ → W ⊩* Δ → W′ ⊩* Δ
    vrens e []       = []
    vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set
    Γ ⊨ A = ∀ {W : Ctx} → W ⊩* Γ → W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs


----------------------------------------------------------------------------------------------------

  module ModelKit
    {Model : Set₁}
    {World : Model → Set}
    {_≤_   : ∀ (ℳ : Model) → World ℳ → World ℳ → Set}
    (_⊩_  : ∀ {ℳ} → World ℳ → Ty → Set)
    (vren : ∀ {ℳ W W′ A} → _≤_ ℳ W W′ → W ⊩ A → W′ ⊩ A)
      where
    module _ {ℳ : Model} where
      -- semantic environments
      infix 3 _⊩*_
      data _⊩*_ (W : World ℳ) : Ctx → Set where
        []  : W ⊩* []
        _∷_ : ∀ {Δ A} (v : W ⊩ A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

      vrens : ∀ {W W′ Δ} → _≤_ ℳ W W′ → W ⊩* Δ → W′ ⊩* Δ
      vrens e []       = []
      vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _/_⊩_
    _/_⊩_ : ∀ (ℳ : Model) (W : World ℳ) → Ty → Set
    ℳ / W ⊩ A = _⊩_ {ℳ} W A

    infix 3 _/_⊩*_
    _/_⊩*_ : ∀ (ℳ : Model) (W : World ℳ) → Ctx → Set
    ℳ / W ⊩* Δ = _⊩*_ {ℳ} W Δ

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set₁
    Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} → ℳ / W ⊩* Γ → ℳ / W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs


----------------------------------------------------------------------------------------------------

  module SplitModelKit
    {BaseModel  : Set₁}
    {SplitModel : BaseModel → Set₁}
    {World      : ∀ {ℳ◦} → SplitModel ℳ◦ → Set}
    {_≤_        : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) → World ℳ → World ℳ → Set}
    (_⊩_       : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) → World ℳ → Ty → Set)
    (vren       : ∀ {ℳ◦} {ℳ : SplitModel ℳ◦} {W W′ A} → _≤_ ℳ W W′ → _⊩_ ℳ W A → _⊩_ ℳ W′ A)
      where
    module _ {ℳ◦} {ℳ : SplitModel ℳ◦} where
      -- semantic environments
      infix 3 _⊩*_
      data _⊩*_ (W : World ℳ) : Ctx → Set where
        []  : W ⊩* []
        _∷_ : ∀ {Δ A} (v : _⊩_ ℳ W A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

      vrens : ∀ {W W′ Δ} → _≤_ ℳ W W′ → W ⊩* Δ → W′ ⊩* Δ
      vrens e []       = []
      vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _/_⊩_
    _/_⊩_ : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) (W : World ℳ) → Ty → Set
    ℳ / W ⊩ A = _⊩_ ℳ W A

    infix 3 _/_⊩*_
    _/_⊩*_ : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) (W : World ℳ) → Ctx → Set
    ℳ / W ⊩* Δ = _⊩*_ {ℳ = ℳ} W Δ

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set₁
    Γ ⊨ A = ∀ {ℳ◦} {ℳ : SplitModel ℳ◦} {W : World ℳ} → ℳ / W ⊩* Γ → ℳ / W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs


----------------------------------------------------------------------------------------------------
