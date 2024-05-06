module A201802.WIP.LocallyNameless where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions

open import A201802.WIP.Bool
open import A201802.WIP.Name
open import A201802.WIP.ListRemovals


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Form → Form → Set
  where
    fvar : ∀ {A Γ} → Name
                   → Γ ⊢ A true

    bvar : ∀ {A Γ} → Γ ∋ A
                   → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true

    pair : ∀ {A B Γ} → Γ ⊢ A true → Γ ⊢ B true
                     → Γ ⊢ A ∧ B true

    fst : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ A true

    snd : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ B true

    unit : ∀ {Γ} → Γ ⊢ 𝟏 true

    abort : ∀ {C Γ} → Γ ⊢ 𝟎 true
                    → Γ ⊢ C true

    inl : ∀ {A B Γ} → Γ ⊢ A true
                    → Γ ⊢ A ∨ B true

    inr : ∀ {A B Γ} → Γ ⊢ B true
                    → Γ ⊢ A ∨ B true

    case : ∀ {A B C Γ} → Γ ⊢ A ∨ B true → Γ , A ⊢ C true → Γ , B ⊢ C true
                       → Γ ⊢ C true


--------------------------------------------------------------------------------


fresh : Name → List Name → Bool
fresh x ∙       = true
fresh x (И , y) = and (x ≠ y) (fresh x И)

_∪_ : List Name → List Name → List Name
И₁ ∪ ∙        = И₁
И₁ ∪ (И₂ , x) with fresh x И₁
И₁ ∪ (И₂ , x) | true  = (И₁ ∪ И₂) , x
И₁ ∪ (И₂ , x) | false = И₁ ∪ И₂

fvs : ∀ {Γ A} → Γ ⊢ A true
              → List Name
fvs (fvar x)     = ∙ , x
fvs (bvar i)     = ∙
fvs (lam 𝒟)      = fvs 𝒟
fvs (app 𝒟 ℰ)    = fvs 𝒟 ∪ fvs ℰ
fvs (pair 𝒟 ℰ)   = fvs 𝒟 ∪ fvs ℰ
fvs (fst 𝒟)      = fvs 𝒟
fvs (snd 𝒟)      = fvs 𝒟
fvs unit         = ∙
fvs (abort 𝒟)    = fvs 𝒟
fvs (inl 𝒟)      = fvs 𝒟
fvs (inr 𝒟)      = fvs 𝒟
fvs (case 𝒟 ℰ ℱ) = fvs 𝒟 ∪ (fvs ℰ ∪ fvs ℱ)

lem∪₁ : ∀ x И₁ И₂ → {{_ : T (fresh x (И₁ ∪ И₂))}}
                  → T (fresh x И₁)
lem∪₁ x И₁ ∙        {{φ}} = φ
lem∪₁ x И₁ (И₂ , y) {{φ}} with fresh y И₁
lem∪₁ x И₁ (И₂ , y) {{φ}} | true  = lem∪₁ x И₁ И₂ {{lem-and₂ x y {{φ}}}}
lem∪₁ x И₁ (И₂ , y) {{φ}} | false = lem∪₁ x И₁ И₂

lid∪ : ∀ И → ∙ ∪ И ≡ И
lid∪ ∙       = refl
lid∪ (И , x) = (_, x) & lid∪ И


-- TODO: unfinished

-- assoc∪ : ∀ И₁ И₂ И₃ → (И₁ ∪ И₂) ∪ И₃ ≡ И₁ ∪ (И₂ ∪ И₃)
-- assoc∪ И₁ И₂       ∙        = refl
-- assoc∪ И₁ ∙        (И₃ , y) with fresh y И₁
-- assoc∪ И₁ ∙        (И₃ , y) | true  rewrite lid∪ И₃ = refl
-- assoc∪ И₁ ∙        (И₃ , y) | false rewrite lid∪ И₃ = refl
-- assoc∪ И₁ (И₂ , x) (И₃ , y) = {!!}

postulate
  lem∪₂ : ∀ x И₁ И₂ → {{_ : T (fresh x (И₁ ∪ И₂))}}
                    → T (fresh x И₂)
-- lem∪₂ x ∙        И₂ {{φ}} rewrite lid∪ И₂ = φ
-- lem∪₂ x (И₁ , y) И₂ {{φ}} = lem∪₂ x И₁ И₂ {{{!!}}}

postulate
  lem∪₃ : ∀ x И₁ И₂ → {{_ : T (fresh x И₁)}} {{_ : T (fresh x И₂)}}
                    → T (fresh x (И₁ ∪ И₂))


--------------------------------------------------------------------------------


-- TODO: unfinished

postulate
  gensym : (И : List Name) → Σ Name (λ x → T (fresh x И))


--------------------------------------------------------------------------------


-- Opening

free : ∀ {Γ A C} x → (i : Γ ∋ A) (𝒟 : Γ ⊢ C true) {{_ : T (fresh x (fvs 𝒟))}} → Γ - i ⊢ C true
free x i (fvar y)     = fvar y
free x i (bvar j)     with i ≟∋ j
free x i (bvar .i)    | same .i   = fvar x
free x i (bvar ._)    | diff .i j = bvar j
free x i (lam 𝒟)      = lam (free x (suc i) 𝒟)
free x i (app 𝒟 ℰ)    = app (free x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ)}})
                            (free x i ℰ {{lem∪₂ x (fvs 𝒟) (fvs ℰ)}})
free x i (pair 𝒟 ℰ)   = pair (free x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ)}})
                             (free x i ℰ {{lem∪₂ x (fvs 𝒟) (fvs ℰ)}})
free x i (fst 𝒟)      = fst (free x i 𝒟)
free x i (snd 𝒟)      = snd (free x i 𝒟)
free x i unit         = unit
free x i (abort 𝒟)    = abort (free x i 𝒟)
free x i (inl 𝒟)      = inl (free x i 𝒟)
free x i (inr 𝒟)      = inr (free x i 𝒟)
free x i (case 𝒟 ℰ ℱ) = case (free x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}})
                             (free x (suc i) ℰ {{lem∪₁ x (fvs ℰ) (fvs ℱ) {{lem∪₂ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}}}})
                             (free x (suc i) ℱ {{lem∪₂ x (fvs ℰ) (fvs ℱ) {{lem∪₂ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}}}})

free-lam : ∀ {Γ A B} x → {𝒟 : Γ , A ⊢ B true}
                          (𝒟′ : Γ ⊢ A ⊃ B true) {{_ : 𝒟′ ≡ lam 𝒟}}
                          {{_ : T (fresh x (fvs 𝒟))}}
                       → Γ ⊢ B true
free-lam x (lam 𝒟) {{refl}} = free x zero 𝒟

free-case : ∀ {Γ A B C} x y → {𝒟 : Γ ⊢ A ∨ B true} {ℰ : Γ , A ⊢ C true} {ℱ : Γ , B ⊢ C true}
                               (𝒟′ : Γ ⊢ C true) {{_ : 𝒟′ ≡ case 𝒟 ℰ ℱ}}
                               {{_ : T (fresh x (fvs ℰ))}} {{_ : T (fresh y (fvs ℱ))}}
                            → Γ ⊢ A ∨ B true × Γ ⊢ C true × Γ ⊢ C true
free-case x y (case 𝒟 ℰ ℱ) {{refl}} = 𝒟 , free x zero ℰ , free y zero ℱ


--------------------------------------------------------------------------------


-- Closing

bind : ∀ {A C Γ} x → (i : Γ ∋ A) (𝒟 : Γ - i ⊢ C true) {{_ : T (fresh x (fvs 𝒟))}}
                   → Σ (Γ ⊢ C true) (\ 𝒟′ → T (fresh x (fvs 𝒟′)))
bind {A} {C} x i (fvar y)        with x ≟ y | A ≟ₚ C
bind {A} {C} x i (fvar .x)       | yes refl | yes refl = bvar i , ∙
bind {A} {C} x i (fvar .x) {{φ}} | yes refl | no A≢C   = elim⊥ φ
bind {A} {C} x i (fvar y)        | no x≢y   | _        = fvar y , lem-and₁ {{≢→≠ x≢y}}
bind         x i (bvar j)        = bvar (ren∋ (del⊇ i) j) , ∙
bind         x i (lam 𝒟)         = let 𝒟′ , φ = bind x (suc i) 𝒟 in lam 𝒟′ , φ
bind         x i (app 𝒟 ℰ)       = let 𝒟′ , φ₁ = bind x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ)}} in
                                   let ℰ′ , φ₂ = bind x i ℰ {{lem∪₂ x (fvs 𝒟) (fvs ℰ)}} in
                                   app 𝒟′ ℰ′ , lem∪₃ x (fvs 𝒟′) (fvs ℰ′) {{φ₁}} {{φ₂}}
bind         x i (pair 𝒟 ℰ)      = let 𝒟′ , φ₁ = bind x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ)}} in
                                   let ℰ′ , φ₂ = bind x i ℰ {{lem∪₂ x (fvs 𝒟) (fvs ℰ)}} in
                                   pair 𝒟′ ℰ′ , lem∪₃ x (fvs 𝒟′) (fvs ℰ′) {{φ₁}} {{φ₂}}
bind         x i (fst 𝒟)         = let 𝒟′ , φ = bind x i 𝒟 in fst 𝒟′ , φ
bind         x i (snd 𝒟)         = let 𝒟′ , φ = bind x i 𝒟 in snd 𝒟′ , φ
bind         x i unit            = unit , ∙
bind         x i (abort 𝒟)       = let 𝒟′ , φ = bind x i 𝒟 in abort 𝒟′ , φ
bind         x i (inl 𝒟)         = let 𝒟′ , φ = bind x i 𝒟 in inl 𝒟′ , φ
bind         x i (inr 𝒟)         = let 𝒟′ , φ = bind x i 𝒟 in inr 𝒟′ , φ
bind         x i (case 𝒟 ℰ ℱ)    = let 𝒟′ , φ₁ = bind x i 𝒟 {{lem∪₁ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}} in
                                   let ℰ′ , φ₂ = bind x (suc i) ℰ {{lem∪₁ x (fvs ℰ) (fvs ℱ) {{lem∪₂ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}}}} in
                                   let ℱ′ , φ₃ = bind x (suc i) ℱ {{lem∪₂ x (fvs ℰ) (fvs ℱ) {{lem∪₂ x (fvs 𝒟) (fvs ℰ ∪ fvs ℱ)}}}} in
                                   case 𝒟′ ℰ′ ℱ′ , lem∪₃ x (fvs 𝒟′) (fvs ℰ′ ∪ fvs ℱ′) {{φ₁}} {{lem∪₃ x (fvs ℰ′) (fvs ℱ′) {{φ₂}} {{φ₃}}}}

-- bind-lam : ∀ {Γ B} x → (𝒟 : Γ ⊢ B true) (i : fvs 𝒟 ∋ x)
--                      → Σ Form (\ A → Γ ⊢ A ⊃ B true) (\ 𝒟′ → 𝒟′ ≡ lam(Γ , A ⊢ B true) (\ 𝒟′ → T (fresh x (fvs 𝒟′)))
-- bind-lam x 𝒟 i = {!!}
--
-- bind-case : ∀ {Γ A B C} x y → (𝒟 : Γ ⊢ A ∨ B true) (ℰ : Γ ⊢ C true) (ℱ : Γ ⊢ C true) (i : fvs ℰ ∋ x) (j : fvs ℱ ∋ y)
--                             → Σ (Γ


--------------------------------------------------------------------------------
