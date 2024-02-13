----------------------------------------------------------------------------------------------------

-- non-deterministic parallel reduction to β-short normal form

module STLC-Base-NF-NDPR where

open import STLC-Base-RenSub public
open import STLC-Base-NF public
open import Kit3 public


----------------------------------------------------------------------------------------------------

-- Schäfer: definition 4.4
infix 4 _▻▻_
data _▻▻_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  var-  : ∀ {A} {i : Γ ∋ A} → var i ▻▻ var i
  congλ : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (r : t ▻▻ t′) → ⌜λ⌝ t ▻▻ ⌜λ⌝ t′
  cong$ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (r₁ : t₁ ▻▻ t₁′) (r₂ : t₂ ▻▻ t₂′) →
          t₁ ⌜$⌝ t₂ ▻▻ t₁′ ⌜$⌝ t₂′
  βred⊃ : ∀ {A B} {t₁ t₁′ : A ∷ Γ ⊢ B} {t₂ t₂′ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁′ [ t₂′ ])
            (r₁ : t₁ ▻▻ t₁′) (r₂ : t₂ ▻▻ t₂′) →
          ⌜λ⌝ t₁ ⌜$⌝ t₂ ▻▻ t′

-- TODO: rename all substitution-related things to disambiguate from reflexive-transitive closure
-- open RedKit1 (kit tmkit _▻▻_) public

-- maximum parallel reduction; Schäfer: ρ
max▻▻ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
max▻▻ (var i)               = var i
max▻▻ (⌜λ⌝ t)               = ⌜λ⌝ (max▻▻ t)
max▻▻ (t₁@(var _) ⌜$⌝ t₂)   = max▻▻ t₁ ⌜$⌝ max▻▻ t₂
max▻▻ (⌜λ⌝ t₁ ⌜$⌝ t₂)       = max▻▻ t₁ [ max▻▻ t₂ ]
max▻▻ (t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂) = max▻▻ t₁ ⌜$⌝ max▻▻ t₂

-- Schäfer: fact 4.5
refl▻▻ : ∀ {Γ A} {t : Γ ⊢ A} → t ▻▻ t
refl▻▻ {t = var i}     = var-
refl▻▻ {t = ⌜λ⌝ t}     = congλ refl▻▻
refl▻▻ {t = t₁ ⌜$⌝ t₂} = cong$ refl▻▻ refl▻▻

ren▻▻ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ▻▻ t′ → ren e t ▻▻ ren e t′
ren▻▻ e var-                           = var-
ren▻▻ e (congλ r)                      = congλ (ren▻▻ (lift⊆ e) r)
ren▻▻ e (cong$ r₁ r₂)                  = cong$ (ren▻▻ e r₁) (ren▻▻ e r₂)
ren▻▻ e (βred⊃ {t₁′ = t₁′} refl r₁ r₂) = βred⊃ (rencut e t₁′ _ ⁻¹) (ren▻▻ (lift⊆ e) r₁)
                                           (ren▻▻ e r₂)

-- Schäfer: lemma 4.6
sub▻▻ : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) {t t′ : Γ ⊢ A} → t ▻▻ t′ → sub ss t ▻▻ sub ss t′
sub▻▻ ss var-                           = refl▻▻
sub▻▻ ss (congλ r)                      = congλ (sub▻▻ (lift* ss) r)
sub▻▻ ss (cong$ r₁ r₂)                  = cong$ (sub▻▻ ss r₁) (sub▻▻ ss r₂)
sub▻▻ ss (βred⊃ {t₁′ = t₁′} refl r₁ r₂) = βred⊃ (subcut ss t₁′ _ ⁻¹) (sub▻▻ (lift* ss) r₁)
                                            (sub▻▻ ss r₂)


----------------------------------------------------------------------------------------------------

-- TODO: prove these definitions equivalent
-- infix 4 _▻▻*_
-- _▻▻*_ : ∀ {Ξ Γ} → Ξ ⊢* Γ → Ξ ⊢* Γ → Set
-- ss ▻▻* ss′ = ∀ {A} (t : _ ⊢ A) → sub ss t ▻▻ sub ss′ t

infix 4 _▻▻*_
data _▻▻*_ {Γ} : ∀ {Δ} → Γ ⊢* Δ → Γ ⊢* Δ → Set where
  []  : [] ▻▻* []
  _∷_ : ∀ {Δ A} {t t′ : Γ ⊢ A} {ts ts′ : Γ ⊢* Δ} (r : t ▻▻ t′) (rs : ts ▻▻* ts′) →
        t ∷ ts ▻▻* t′ ∷ ts′

-- TODO: kit?
ren▻▻* : ∀ {Γ Γ′ Δ} {ts ts′ : Γ ⊢* Δ} (e : Γ ⊆ Γ′) → ts ▻▻* ts′ → ren* e ts ▻▻* ren* e ts′
ren▻▻* e []       = []
ren▻▻* e (r ∷ rs) = ren▻▻ e r ∷ ren▻▻* e rs

wk▻▻* : ∀ {Γ Δ B} {ts ts′ : Γ ⊢* Δ} → ts ▻▻* ts′ → wk* ts ▻▻* wk* {B} ts′
wk▻▻* rs = ren▻▻* (wk⊆ id⊆) rs

-- Schäfer: corollary 4.7
lift▻▻* : ∀ {Γ Δ B} {ts ts′ : Γ ⊢* Δ} → ts ▻▻* ts′ → lift* ts ▻▻* lift* {B} ts′
lift▻▻* rs = var- ∷ wk▻▻* rs

var▻▻* : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → var* e ▻▻* var* e
var▻▻* stop⊆     = []
var▻▻* (wk⊆ e)   = wk▻▻* (var▻▻* e)
var▻▻* (lift⊆ e) = lift▻▻* (var▻▻* e)

id▻▻* : ∀ {Γ} → id* ▻▻* id* {Γ}
id▻▻* {[]}    = []
id▻▻* {A ∷ Γ} = lift▻▻* id▻▻*

sub▻▻* : ∀ {Γ Δ Ξ} {ts ts′ : Γ ⊢* Δ} (ss : Ξ ⊢* Γ) → ts ▻▻* ts′ → sub* ss ts ▻▻* sub* ss ts′
sub▻▻* ss []       = []
sub▻▻* ss (r ∷ rs) = sub▻▻ ss r ∷ sub▻▻* ss rs

lem-4-8-∋ : ∀ {Γ Ξ A} {ss ss′ : Ξ ⊢* Γ} {i : Γ ∋ A} → ss ▻▻* ss′ → sub∋ ss i ▻▻ sub∋ ss′ i
lem-4-8-∋ {i = zero}  (r ∷ rs) = r
lem-4-8-∋ {i = suc i} (r ∷ rs) = lem-4-8-∋ rs

-- Schäfer: lemma 4.8
lem-4-8 : ∀ {Γ Ξ A} {ss ss′ : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → ss ▻▻* ss′ → t ▻▻ t′ →
          sub ss t ▻▻ sub ss′ t′
lem-4-8 rs var-                           = lem-4-8-∋ rs
lem-4-8 rs (congλ r)                      = congλ (lem-4-8 (lift▻▻* rs) r)
lem-4-8 rs (cong$ r₁ r₂)                  = cong$ (lem-4-8 rs r₁) (lem-4-8 rs r₂)
lem-4-8 rs (βred⊃ {t₁′ = t₁′} refl r₁ r₂) = βred⊃ (subcut _ t₁′ _ ⁻¹) (lem-4-8 (lift▻▻* rs) r₁)
                                              (lem-4-8 rs r₂)

-- Schäfer: lemma 4.9
lem-4-9 : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ▻▻ t′ → t′ ▻▻ max▻▻ t
lem-4-9 var-                                = var-
lem-4-9 (congλ r)                           = congλ (lem-4-9 r)
lem-4-9 (cong$ {t₁ = t₁@(var _)} r₁ r₂)     = cong$ (lem-4-9 r₁) (lem-4-9 r₂)
lem-4-9 (cong$ {t₁ = ⌜λ⌝ t₁} (congλ r₁) r₂) = βred⊃ refl (lem-4-9 r₁) (lem-4-9 r₂)
lem-4-9 (cong$ {t₁ = t₁@(_ ⌜$⌝ _)} r₁ r₂)   = cong$ (lem-4-9 r₁) (lem-4-9 r₂)
lem-4-9 (βred⊃ {t₁ = t₁} refl r₁ r₂)        = lem-4-8 (lem-4-9 r₂ ∷ id▻▻*) (lem-4-9 r₁)

-- Schäfer: lemma 4.10; TODO
-- "From lemma 49 we conclude that parallel reduction has the diamond property and hence by
-- corollary 2.14 that parallel reduction is confluent."


----------------------------------------------------------------------------------------------------
