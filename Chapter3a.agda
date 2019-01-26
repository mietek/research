module Chapter3a where

open import Chapter3 public


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.16. Exercise [Recommended, ⋆⋆⋆]
-- (continued)
-- “Show that these two treatments of run-time errors agree by (1) finding a precise way of stating the
-- intuition that “the two treatments agree,” and (2) proving it.”
--
-- We’re going to show that expressions-that-go-wrong go wrong exactly when expressions-that-get-stuck get
-- stuck.  In order to do so, we’re going to need a type of terms that are _wrongless_, i.e., that do not
-- contain `wrong` as a subterm.  For this purpose, we define a predicate on terms, `Wrongless`.

module NumbersAndBooleansGoWrong-Part2
  where
    open NumbersAndBooleansGoWrong-Part1 public

    data Wrongless : Pred₀ Term where
      true         : Wrongless true
      false        : Wrongless false
      zero         : Wrongless zero
      suc          : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (suc t)
      pred         : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (pred t)
      iszero       : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (iszero t)
      if_then_else : ∀ {t₁ t₂ t₃} → (ρₜ₁ : Wrongless t₁) (ρₜ₂ : Wrongless t₂) (ρₜ₃ : Wrongless t₃) →
                     Wrongless (if t₁ then t₂ else t₃)


-- We say that a one-step reduction from `t` to `u` is wrongless when `u` is wrongless.  A multi-step
-- reduction is wrongless when it is composed of wrongless reductions.

    data WronglessReds : ∀ {t u} → Pred₀ (t ⟹* u) where
      []  : ∀ {t} → WronglessReds {t} {t} []
      _∷_ : ∀ {t x u} {t⟹x : t ⟹ x} {x⟹*u : x ⟹* u} →
            (ρₓ : Wrongless x) (ρᵣₛ : WronglessReds x⟹*u) → WronglessReds (t⟹x ∷ x⟹*u)


-- The evidence that a term is wrongless is unique.

    ρ-uniq : ∀ {t} → (ρₜ ρₜ′ : Wrongless t) → ρₜ ≡ ρₜ′
    ρ-uniq true        true         = refl
    ρ-uniq false       false        = refl
    ρ-uniq zero        zero         = refl
    ρ-uniq (suc ρₜ)    (suc ρₜ′)    with ρ-uniq ρₜ ρₜ′
    ... | refl                      = refl
    ρ-uniq (pred ρₜ)   (pred ρₜ′)   with ρ-uniq ρₜ ρₜ′
    ... | refl                      = refl
    ρ-uniq (iszero ρₜ) (iszero ρₜ′) with ρ-uniq ρₜ ρₜ′
    ... | refl                      = refl
    ρ-uniq (if ρₜ₁ then ρₜ₂ else ρₜ₃)
                       (if ρₜ₁′ then ρₜ₂′ else ρₜ₃′)
                                    with ρ-uniq ρₜ₁ ρₜ₁′ | ρ-uniq ρₜ₂ ρₜ₂′ | ρ-uniq ρₜ₃ ρₜ₃′
    ... | refl | refl | refl        = refl


-- We can decide whether a term is wrongless or not.

    ρ? : ∀ t → Dec (Wrongless t)
    ρ? wrong                          = no λ ()
    ρ? true                           = yes true
    ρ? false                          = yes false
    ρ? zero                           = yes zero
    ρ? (suc t)                        with ρ? t
    ... | yes ρₜ                      = yes (suc ρₜ)
    ... | no ¬ρₜ                      = no λ where (suc ρₜ) → ρₜ ↯ ¬ρₜ
    ρ? (pred t)                       with ρ? t
    ... | yes ρₜ                      = yes (pred ρₜ)
    ... | no ¬ρₜ                      = no λ where (pred ρₜ) → ρₜ ↯ ¬ρₜ
    ρ? (iszero t)                     with ρ? t
    ... | yes ρₜ                      = yes (iszero ρₜ)
    ... | no ¬ρₜ                      = no λ where (iszero ρₜ) → ρₜ ↯ ¬ρₜ
    ρ? (if t₁ then t₂ else t₃)        with ρ? t₁ | ρ? t₂ | ρ? t₃
    ... | no ¬ρₜ₁ | _       | _       = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₁ ↯ ¬ρₜ₁
    ... | yes ρₜ₁ | no ¬ρₜ₂ | _       = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₂ ↯ ¬ρₜ₂
    ... | yes ρₜ₁ | yes ρₜ₂ | no ¬ρₜ₃ = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₃ ↯ ¬ρₜ₃
    ... | yes ρₜ₁ | yes ρₜ₂ | yes ρₜ₃ = yes (if ρₜ₁ then ρₜ₂ else ρₜ₃)


---------------------------------------------------------------------------------------------------------------
--
-- Original terms and reductions can be translated to the augmented system.

open module O = NumbersAndBooleansGetStuck
  renaming (_⟹_ to O[_⟹_] ; _⟹*_ to O[_⟹*_])

open module W = NumbersAndBooleansGoWrong-Part2
  renaming (_⟹_ to W[_⟹_] ; _⟹*_ to W[_⟹*_])

o→w : O.Term → W.Term
o→w true                    = true
o→w false                   = false
o→w zero                    = zero
o→w (suc t)                 = suc (o→w t)
o→w (pred t)                = pred (o→w t)
o→w (iszero t)              = iszero (o→w t)
o→w (if t₁ then t₂ else t₃) = if (o→w t₁) then (o→w t₂) else (o→w t₃)

onv→wnv : ∀ {t} → O.NumericValue t → W.NumericValue (o→w t)
onv→wnv zero      = zero
onv→wnv (suc nvₜ) = suc (onv→wnv nvₜ)

ov→wv : ∀ {t} → O.Value t → W.Value (o→w t)
ov→wv true      = true
ov→wv false     = false
ov→wv (num nvₜ) = num (onv→wnv nvₜ)

or→wr : ∀ {t u} → O[ t ⟹ u ] → W[ o→w t ⟹ o→w u ]
or→wr (r-suc t⟹u)     = r-suc (or→wr t⟹u)
or→wr r-predZero        = r-predZero
or→wr (r-predSuc nvₜ)   = r-predSuc (onv→wnv nvₜ)
or→wr (r-pred t⟹u)    = r-pred (or→wr t⟹u)
or→wr r-iszeroZero      = r-iszeroZero
or→wr (r-iszeroSuc nvₜ) = r-iszeroSuc (onv→wnv nvₜ)
or→wr (r-iszero t⟹u)  = r-iszero (or→wr t⟹u)
or→wr r-ifTrue          = r-ifTrue
or→wr r-ifFalse         = r-ifFalse
or→wr (r-if t₁⟹u₁)    = r-if (or→wr t₁⟹u₁)


-- Augmented wrongless terms and reductions can be translated to the original system.

w→o : ∀ {t} → Wrongless t → O.Term
w→o true                       = true
w→o false                      = false
w→o zero                       = zero
w→o (suc ρₜ)                   = suc (w→o ρₜ)
w→o (pred ρₜ)                  = pred (w→o ρₜ)
w→o (iszero ρₜ)                = iszero (w→o ρₜ)
w→o (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if (w→o ρₜ₁) then (w→o ρₜ₂) else (w→o ρₜ₃)

wnv→onv : ∀ {t} → (ρₜ : Wrongless t) → W.NumericValue t → O.NumericValue (w→o ρₜ)
wnv→onv zero     zero      = zero
wnv→onv (suc ρₜ) (suc nvₜ) = suc (wnv→onv ρₜ nvₜ)

wr→or : ∀ {t u} → (ρₜ : Wrongless t) (ρᵤ : Wrongless u) → W[ t ⟹ u ] → O[ w→o ρₜ ⟹ w→o ρᵤ ]
wr→or _                 ()          (r-sucWrong _)
wr→or (suc ρₜ)          (suc ρᵤ)    (r-suc t⟹u)     = r-suc (wr→or ρₜ ρᵤ t⟹u)
wr→or _                 ()          (r-predWrong _)
wr→or (pred zero)       zero        r-predZero        = r-predZero
wr→or (pred (suc ρₜ))   ρₜ′         (r-predSuc nvₜ)   with ρ-uniq ρₜ ρₜ′
... | refl                                             = r-predSuc (wnv→onv ρₜ nvₜ)
wr→or (pred ρₜ)         (pred ρᵤ)   (r-pred t⟹u)    = r-pred (wr→or ρₜ ρᵤ t⟹u)
wr→or _                 ()          (r-iszeroWrong _)
wr→or (iszero zero)     true        r-iszeroZero      = r-iszeroZero
wr→or (iszero (suc ρₜ)) false       (r-iszeroSuc nvₜ) = r-iszeroSuc (wnv→onv ρₜ nvₜ)
wr→or (iszero ρₜ)       (iszero ρᵤ) (r-iszero t⟹u)  = r-iszero (wr→or ρₜ ρᵤ t⟹u)
wr→or _                 ()          (r-ifWrong _)
wr→or (if true then ρₜ₂ else ρₜ₃)
                         ρᵤ          r-ifTrue          with ρ-uniq ρₜ₂ ρᵤ
... | refl                                             = r-ifTrue
wr→or (if false then ρₜ₂ else ρₜ₃)
                         ρᵤ          r-ifFalse         with ρ-uniq ρₜ₃ ρᵤ
... | refl                                             = r-ifFalse
wr→or (if ρₜ₁ then ρₜ₂ else ρₜ₃)
                         (if ρᵤ₁ then ρₜ₂′ else ρₜ₃′)
                                     (r-if t₁⟹u₁)    with ρ-uniq ρₜ₂ ρₜ₂′ | ρ-uniq ρₜ₃ ρₜ₃′
... | refl | refl                                      = r-if (wr→or ρₜ₁ ρᵤ₁ t₁⟹u₁)

wrs→ors : ∀ {t u} → (ρₜ : Wrongless t) (ρᵤ : Wrongless u) →
           {t⟹*u : W[ t ⟹* u ]} → WronglessReds t⟹*u → O[ w→o ρₜ ⟹* w→o ρᵤ ]
wrs→ors ρₜ ρᵤ {[]}             []         with ρ-uniq ρₜ ρᵤ
... | refl                                 = []
wrs→ors ρₜ ρᵤ {t⟹x ∷ x⟹*u} (ρₓ ∷ ρᵣₛ) = wr→or ρₜ ρₓ t⟹x ∷ wrs→ors ρₓ ρᵤ ρᵣₛ


-- Translating an original term to the augmented system produces a wrongless term.

ρ! : ∀ t → Wrongless (o→w t)
ρ! true                    = true
ρ! false                   = false
ρ! zero                    = zero
ρ! (suc t)                 = suc (ρ! t)
ρ! (pred t)                = pred (ρ! t)
ρ! (iszero t)              = iszero (ρ! t)
ρ! (if t₁ then t₂ else t₃) = if (ρ! t₁) then (ρ! t₂) else (ρ! t₃)


-- Translating a term forth and back produces an identical term.

wow-id : ∀ {t} → (ρₜ : Wrongless t) → o→w (w→o ρₜ) ≡ t
wow-id true                       = refl
wow-id false                      = refl
wow-id zero                       = refl
wow-id (suc ρₜ)                   = suc & wow-id ρₜ
wow-id (pred ρₜ)                  = pred & wow-id ρₜ
wow-id (iszero ρₜ)                = iszero & wow-id ρₜ
wow-id (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if_then_else &
                                    wow-id ρₜ₁ ⊗ wow-id ρₜ₂ ⊗ wow-id ρₜ₃

owo-id : ∀ {t} → (ρₜ : Wrongless (o→w t)) → w→o ρₜ ≡ t
owo-id {true}               true                       = refl
owo-id {false}              false                      = refl
owo-id {zero}               zero                       = refl
owo-id {suc _}              (suc ρₜ)                   = suc & owo-id ρₜ
owo-id {pred _}             (pred ρₜ)                  = pred & owo-id ρₜ
owo-id {iszero _}           (iszero ρₜ)                = iszero & owo-id ρₜ
owo-id {if _ then _ else _} (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if_then_else &
                                                         owo-id ρₜ₁ ⊗ owo-id ρₜ₂ ⊗ owo-id ρₜ₃


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.4.
-- “If `t` is stuck then `W[ t ⟹* wrong ]`.”

lem-a4 : ∀ {t} → O.Stuck t → W[ o→w t ⟹* wrong ]
lem-a4 {true}                  (¬vₜ , _)    = true ↯ ¬vₜ
lem-a4 {false}                 (¬vₜ , _)    = false ↯ ¬vₜ
lem-a4 {zero}                  (¬vₜ , _)    = num zero ↯ ¬vₜ
lem-a4 {suc t}                 (¬vₜ , nfₜ)  with O.classify t
... | stu σₜ                                = map r-suc (lem-a4 σₜ) ∷ʳ r-sucWrong wrong
... | val true                              = r-sucWrong true ∷ []
... | val false                             = r-sucWrong false ∷ []
... | val (num nvₜ)                         = num (suc nvₜ) ↯ ¬vₜ
... | red (_ , t⟹u)                       = r-suc t⟹u ↯ nfₜ
lem-a4 {pred t}                (_   , nfₜ)  with O.classify t
... | stu σₜ                                = map r-pred (lem-a4 σₜ) ∷ʳ r-predWrong wrong
... | val true                              = r-predWrong true ∷ []
... | val false                             = r-predWrong false ∷ []
... | val (num zero)                        = r-predZero ↯ nfₜ
... | val (num (suc nvₜ))                   = r-predSuc nvₜ ↯ nfₜ
... | red (_ , t⟹u)                       = r-pred t⟹u ↯ nfₜ
lem-a4 {iszero t}              (_   , nfₜ)  with O.classify t
... | stu σₜ                                = map r-iszero (lem-a4 σₜ) ∷ʳ r-iszeroWrong wrong
... | val true                              = r-iszeroWrong true ∷ []
... | val false                             = r-iszeroWrong false ∷ []
... | val (num zero)                        = r-iszeroZero ↯ nfₜ
... | val (num (suc nvₜ))                   = r-iszeroSuc nvₜ ↯ nfₜ
... | red (_ , t⟹u)                       = r-iszero t⟹u ↯ nfₜ
lem-a4 {if t₁ then t₂ else t₃} (_   , nfₜ₁) with O.classify t₁
... | stu σₜ₁                               = map r-if (lem-a4 σₜ₁) ∷ʳ r-ifWrong wrong
... | val true                              = r-ifTrue ↯ nfₜ₁
... | val false                             = r-ifFalse ↯ nfₜ₁
... | val (num nvₜ₁)                        = r-ifWrong (num (onv→wnv nvₜ₁)) ∷ []
... | red (_ , t₁⟹u₁)                     = r-if t₁⟹u₁ ↯ nfₜ₁


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.5.
-- “If `W[ t ⟹ u ]` in the augmented semantics and `u` contains `wrong` as a subterm, then `t` is stuck in
-- the original semantics.”

lem-a5 : ∀ {t u} → ¬ Wrongless u → W[ o→w t ⟹ u ] → O.Stuck t
lem-a5 {t} ¬ρᵤ t⟹u   with O.classify t
... | stu σₜ           = σₜ
... | val vₜ           = t⟹u ↯ W.v→nf (ov→wv vₜ)
... | red (u , t⟹u′) with W.⟹-det t⟹u (or→wr t⟹u′)
... | refl             = ρ! u ↯ ¬ρᵤ


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.2.
-- “For all original terms `t`, (`O[ t ⟹* u ]` where `u` is stuck) iff (`W[ t ⟹* wrong ]`).”
--
-- The left-to-right implication follows from Lemma A.4.

prop-a2-ltr : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⟹* u ]) → W[ o→w t ⟹* wrong ]
prop-a2-ltr (u , σ , [])     = lem-a4 σ
prop-a2-ltr (u , σ , r ∷ rs) = or→wr r ∷ prop-a2-ltr (u , σ , rs)


-- To show the right-to-left implication, we’re going to find the first wrongless term `u` in our multi-step
-- reduction that reduces to a non-wrongless term.

prop-a2-find : ∀ {t} → Wrongless t → W[ t ⟹* wrong ] →
               ∃ λ u → Wrongless u × Σ W[ t ⟹* u ] WronglessReds ×
               ∃ λ v → ¬ Wrongless v × W[ u ⟹ v ]
prop-a2-find {t} () []
prop-a2-find {t} ρₜ (t⟹x ∷⟨ x ⟩ x⟹*wrong) with ρ? x
... | no ¬ρₓ                  = t , ρₜ , ([] , []) , x , ¬ρₓ , t⟹x
... | yes ρₓ                  with prop-a2-find ρₓ x⟹*wrong
... | u , ρᵤ , (x⟹*u , ρᵣₛ)
    , v , ¬ρᵥ , u⟹v         = u , ρᵤ , (t⟹x ∷ x⟹*u , ρₓ ∷ ρᵣₛ)
                              , v , ¬ρᵥ , u⟹v


-- Then, all that remains to be done is massaging the evidence into the desired form.

r-wow-id : ∀ {t u} → (ρₜ : Wrongless t) → W[ t ⟹ u ] ≡ W[ o→w (w→o ρₜ) ⟹ u ]
r-wow-id ρₜ rewrite wow-id ρₜ = refl

rs-wow-id : ∀ {t u} → (ρᵤ : Wrongless u) → W[ t ⟹* u ] ≡ W[ t ⟹* o→w (w→o ρᵤ) ]
rs-wow-id ρᵤ rewrite wow-id ρᵤ = refl

ρs-wow-id : ∀ {t u} {t⟹*u : W[ o→w t ⟹* u ]} → (ρᵤ : Wrongless u) →
            WronglessReds t⟹*u ≡ WronglessReds (coerce t⟹*u (rs-wow-id ρᵤ))
ρs-wow-id ρᵤ rewrite wow-id ρᵤ = refl

rs-owo-id : ∀ {t u} → (ρₜ : Wrongless (o→w t)) (ρᵤ : Wrongless (o→w u)) →
            O[ w→o ρₜ ⟹* w→o ρᵤ ] ≡ O[ t ⟹* u ]
rs-owo-id ρₜ ρᵤ rewrite owo-id ρₜ | owo-id ρᵤ = refl

prop-a2-rtl : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → O.Stuck u × O[ t ⟹* u ])
prop-a2-rtl {t} t⟹*wrong            with prop-a2-find (ρ! t) t⟹*wrong
... | [u] , [ρᵤ] , ([t⟹*u] , [ρᵣₛ])
    , v   , ¬ρᵥ  , [u⟹v]            =
  let
    u      = w→o [ρᵤ]
    t⟹*u = coerce [t⟹*u] (rs-wow-id [ρᵤ])
    ρᵣₛ    = coerce [ρᵣₛ] (ρs-wow-id [ρᵤ])
    u⟹v  = coerce [u⟹v] (r-wow-id [ρᵤ])
    σᵤ     = lem-a5 ¬ρᵥ u⟹v
    ρₜ     = ρ! t
    ρᵤ     = ρ! u
  in
    u , σᵤ , coerce (wrs→ors ρₜ ρᵤ ρᵣₛ) (rs-owo-id ρₜ ρᵤ)


-- Finally, we conclude Exercise 3.5.16.

prop-a2 : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⟹* u ]) ↔ W[ o→w t ⟹* wrong ]
prop-a2 = prop-a2-ltr , prop-a2-rtl


---------------------------------------------------------------------------------------------------------------
