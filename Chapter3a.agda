module Chapter3a where

open import Chapter3 public


----------------------------------------------------------------------------------------------------
--
-- TODO

module NumbersAndBooleansGoWrong-Part2
  where
    open NumbersAndBooleansGoWrong-Part1 public


    data GoodTerm : Pred₀ Term where
      true         : GoodTerm true
      false        : GoodTerm false
      zero         : GoodTerm zero
      suc          : ∀ {t} → (gt : GoodTerm t) → GoodTerm (suc t)
      pred         : ∀ {t} → (gt : GoodTerm t) → GoodTerm (pred t)
      iszero       : ∀ {t} → (gt : GoodTerm t) → GoodTerm (iszero t)
      if_then_else : ∀ {t₁ t₂ t₃} → (gt₁ : GoodTerm t₁) (gt₂ : GoodTerm t₂) (gt₃ : GoodTerm t₃) →
                     GoodTerm (if t₁ then t₂ else t₃)

    gt-uniq : ∀ {t} → (gt gt′ : GoodTerm t) → gt ≡ gt′
    gt-uniq true                       true                          = refl
    gt-uniq false                      false                         = refl
    gt-uniq zero                       zero                          = refl
    gt-uniq (suc gt)                   (suc gt′)                     with gt-uniq gt gt′
    ... | refl                                                        = refl
    gt-uniq (pred gt)                  (pred gt′)                    with gt-uniq gt gt′
    ... | refl                                                       = refl
    gt-uniq (iszero gt)                (iszero gt′)                  with gt-uniq gt gt′
    ... | refl                                                       = refl
    gt-uniq (if gt₁ then gt₂ else gt₃) (if gt₁′ then gt₂′ else gt₃′) with gt-uniq gt₁ gt₁′ | gt-uniq gt₂ gt₂′ | gt-uniq gt₃ gt₃′
    ... | refl | refl | refl                                         = refl

    good? : ∀ t → Dec (GoodTerm t)
    good? wrong                       = no λ ()
    good? true                        = yes true
    good? false                       = yes false
    good? zero                        = yes zero
    good? (suc t)                     with good? t
    ... | yes gₜ                      = yes (suc gₜ)
    ... | no ¬gₜ                      = no λ where (suc gₜ) → gₜ ↯ ¬gₜ
    good? (pred t)                    with good? t
    ... | yes gₜ                      = yes (pred gₜ)
    ... | no ¬gₜ                      = no λ where (pred gₜ) → gₜ ↯ ¬gₜ
    good? (iszero t)                  with good? t
    ... | yes gₜ                      = yes (iszero gₜ)
    ... | no ¬gₜ                      = no λ where (iszero gₜ) → gₜ ↯ ¬gₜ
    good? (if t₁ then t₂ else t₃)     with good? t₁ | good? t₂ | good? t₃
    ... | no ¬gₜ₁ | _ | _             = no λ where (if gₜ₁ then gₜ₂ else gₜ₃) → gₜ₁ ↯ ¬gₜ₁
    ... | yes gₜ₁ | no ¬gₜ₂ | _       = no λ where (if gₜ₁ then gₜ₂ else gₜ₃) → gₜ₂ ↯ ¬gₜ₂
    ... | yes gₜ₁ | yes gₜ₂ | no ¬gₜ₃ = no λ where (if gₜ₁ then gₜ₂ else gₜ₃) → gₜ₃ ↯ ¬gₜ₃
    ... | yes gₜ₁ | yes gₜ₂ | yes gₜ₃ = yes (if gₜ₁ then gₜ₂ else gₜ₃)

    data GoodReds : ∀ {t u} → Pred₀ (t ⟹* u) where
      []  : ∀ {t} → GoodReds {t} {t} []
      _∷_ : ∀ {s t u} {r : s ⟹ t} {rs : t ⟹* u} →
            GoodTerm t → GoodReds rs → GoodReds (r ∷ rs)


----------------------------------------------------------------------------------------------------
--
-- TODO

open module O = NumbersAndBooleansGetStuck
  renaming (_⟹_ to O[_⟹_] ; _⟹*_ to O[_⟹*_] ; _⟹*′_ to O[_⟹*′_])

open module W = NumbersAndBooleansGoWrong-Part2
  renaming (_⟹_ to W[_⟹_] ; _⟹*_ to W[_⟹*_] ; _⟹*′_ to W[_⟹*′_])


----------------------------------------------------------------------------------------------------
--
-- Conversion from the original system to the system augmented with `wrong`.

o→w : O.Term → W.Term
o→w true                    = true
o→w false                   = false
o→w zero                    = zero
o→w (suc t)                 = suc (o→w t)
o→w (pred t)                = pred (o→w t)
o→w (iszero t)              = iszero (o→w t)
o→w (if t₁ then t₂ else t₃) = if (o→w t₁) then (o→w t₂) else (o→w t₃)

onv→wnv : ∀ {t} → O.NumericValue t → W.NumericValue (o→w t)
onv→wnv zero     = zero
onv→wnv (suc nv) = suc (onv→wnv nv)

ov→wv : ∀ {t} → O.Value t → W.Value (o→w t)
ov→wv true     = true
ov→wv false    = false
ov→wv (num nv) = num (onv→wnv nv)

or→wr : ∀ {t u} → O[ t ⟹ u ] → W[ o→w t ⟹ o→w u ]
or→wr (r-suc r)        = r-suc (or→wr r)
or→wr r-predZero       = r-predZero
or→wr (r-predSuc nv)   = r-predSuc (onv→wnv nv)
or→wr (r-pred r)       = r-pred (or→wr r)
or→wr r-iszeroZero     = r-iszeroZero
or→wr (r-iszeroSuc nv) = r-iszeroSuc (onv→wnv nv)
or→wr (r-iszero r)     = r-iszero (or→wr r)
or→wr r-ifTrue         = r-ifTrue
or→wr r-ifFalse        = r-ifFalse
or→wr (r-if r)         = r-if (or→wr r)


----------------------------------------------------------------------------------------------------
--
-- Conversion from the system augmented with `wrong` to the original system.

w→o : ∀ {t} → GoodTerm t → O.Term
w→o true                       = true
w→o false                      = false
w→o zero                       = zero
w→o (suc gt)                   = suc (w→o gt)
w→o (pred gt)                  = pred (w→o gt)
w→o (iszero gt)                = iszero (w→o gt)
w→o (if gt₁ then gt₂ else gt₃) = if (w→o gt₁) then (w→o gt₂) else (w→o gt₃)

wnv→onv : ∀ {t} → (gt : GoodTerm t) → W.NumericValue t → O.NumericValue (w→o gt)
wnv→onv zero     zero     = zero
wnv→onv (suc gt) (suc nv) = suc (wnv→onv gt nv)

wr→or : ∀ {t u} → (gt : GoodTerm t) (gu : GoodTerm u) → W[ t ⟹ u ] → O[ w→o gt ⟹ w→o gu ]
wr→or _                            ()                         (r-sucWrong _)
wr→or (suc gt)                     (suc gu)                   (r-suc r)         = r-suc (wr→or gt gu r)
wr→or _                            ()                         (r-predWrong _)
wr→or (pred zero)                  zero                       r-predZero        = r-predZero
wr→or (pred (suc gt))              gu                         (r-predSuc nv)    with gt-uniq gt gu
... | refl                                                                       = r-predSuc (wnv→onv gt nv)
wr→or (pred gt)                    (pred gu)                  (r-pred r)        = r-pred (wr→or gt gu r)
wr→or _                            ()                         (r-iszeroWrong _)
wr→or (iszero zero)                true                       r-iszeroZero      = r-iszeroZero
wr→or (iszero (suc gt))            false                      (r-iszeroSuc nv)  = r-iszeroSuc (wnv→onv gt nv)
wr→or (iszero gt)                  (iszero gu)                (r-iszero r)      = r-iszero (wr→or gt gu r)
wr→or _                            ()                         (r-ifWrong _)
wr→or (if true then gt₂ else gt₃)  gu                         r-ifTrue          with gt-uniq gt₂ gu
... | refl                                                                       = r-ifTrue
wr→or (if false then gt₂ else gt₃) gu                         r-ifFalse         with gt-uniq gt₃ gu
... | refl                                                                       = r-ifFalse
wr→or (if gt₁ then gt₂ else gt₃)   (if gu₁ then gu₂ else gu₃) (r-if r)          with gt-uniq gt₂ gu₂ | gt-uniq gt₃ gu₃
... | refl | refl                                                                = r-if (wr→or gt₁ gu₁ r)

wrs→ors : ∀ {t u} → (gt : GoodTerm t) (gu : GoodTerm u) (rs : W[ t ⟹* u ]) → GoodReds rs →
           O[ w→o gt ⟹* w→o gu ]
wrs→ors gt gu []       []         with gt-uniq gt gu
... | refl                         = []
wrs→ors gt gu (r ∷ rs) (gy ∷ grs) = wr→or gt gy r ∷ wrs→ors gy gu rs grs


----------------------------------------------------------------------------------------------------
--
-- Lemma A.4.
-- “If `t` is stuck then `W[ t ⟹* wrong ]`.”

lem-a4 : ∀ {t} → O.Stuck t → W[ o→w t ⟹* wrong ]
lem-a4 {true}                  (¬v , nf) = true ↯ ¬v
lem-a4 {false}                 (¬v , nf) = false ↯ ¬v
lem-a4 {zero}                  (¬v , nf) = num zero ↯ ¬v
lem-a4 {suc t}                 (¬v , nf) with O.classify t
... | stu σ                              = map r-suc (lem-a4 σ) ∷ʳ r-sucWrong wrong
... | val true                           = r-sucWrong true ∷ []
... | val false                          = r-sucWrong false ∷ []
... | val (num nv)                       = num (suc nv) ↯ ¬v
... | red (_ , r)                        = r-suc r ↯ nf
lem-a4 {pred t}                (¬v , nf) with O.classify t
... | stu σ                              = map r-pred (lem-a4 σ) ∷ʳ r-predWrong wrong
... | val true                           = r-predWrong true ∷ []
... | val false                          = r-predWrong false ∷ []
... | val (num zero)                     = r-predZero ↯ nf
... | val (num (suc nv))                 = r-predSuc nv ↯ nf
... | red (_ , r)                        = r-pred r ↯ nf
lem-a4 {iszero t}              (¬v , nf) with O.classify t
... | stu σ                              = map r-iszero (lem-a4 σ) ∷ʳ r-iszeroWrong wrong
... | val true                           = r-iszeroWrong true ∷ []
... | val false                          = r-iszeroWrong false ∷ []
... | val (num zero)                     = r-iszeroZero ↯ nf
... | val (num (suc nv))                 = r-iszeroSuc nv ↯ nf
... | red (_ , r)                        = r-iszero r ↯ nf
lem-a4 {if t₁ then t₂ else t₃} (¬v , nf) with O.classify t₁
... | stu σ₁                             = map r-if (lem-a4 σ₁) ∷ʳ r-ifWrong wrong
... | val true                           = r-ifTrue ↯ nf
... | val false                          = r-ifFalse ↯ nf
... | val (num nv₁)                      = r-ifWrong (num (onv→wnv nv₁)) ∷ []
... | red (_ , r₁)                       = r-if r₁ ↯ nf


----------------------------------------------------------------------------------------------------
--
-- TODO

help-0 : ∀ t → GoodTerm (o→w t)
help-0 true                    = true
help-0 false                   = false
help-0 zero                    = zero
help-0 (suc t)                 = suc (help-0 t)
help-0 (pred t)                = pred (help-0 t)
help-0 (iszero t)              = iszero (help-0 t)
help-0 (if t₁ then t₂ else t₃) = if (help-0 t₁) then (help-0 t₂) else (help-0 t₃)

help-3a : ∀ {t} → (gt : GoodTerm (o→w t)) → w→o gt ≡ t
help-3a {true}                  true                       = refl
help-3a {false}                 false                      = refl
help-3a {zero}                  zero                       = refl
help-3a {suc t}                 (suc gt)                   = suc & help-3a gt
help-3a {pred t}                (pred gt)                  = pred & help-3a gt
help-3a {iszero t}              (iszero gt)                = iszero & help-3a gt
help-3a {if t₁ then t₂ else t₃} (if gt₁ then gt₂ else gt₃) = if_then_else & help-3a gt₁ ⊗ help-3a gt₂ ⊗ help-3a gt₃

help-1 : ∀ {t} → (gt : GoodTerm t) → o→w (w→o gt) ≡ t
help-1 true                       = refl
help-1 false                      = refl
help-1 zero                       = refl
help-1 (suc gt)                   = suc & help-1 gt
help-1 (pred gt)                  = pred & help-1 gt
help-1 (iszero gt)                = iszero & help-1 gt
help-1 (if gt₁ then gt₂ else gt₃) = if_then_else & help-1 gt₁ ⊗ help-1 gt₂ ⊗ help-1 gt₃


----------------------------------------------------------------------------------------------------
--
-- Lemma A.5.
-- “If `W[ t ⟹ u ]` in the augmented semantics and `u` contains `wrong` as a subterm, then `t` is
-- stuck in the original semantics.”

lem-a5 : ∀ {u v} → (¬gv : ¬ GoodTerm v) → W[ o→w u ⟹ v ] → O.Stuck u
lem-a5 {u} ¬gv r with O.classify u
lem-a5 {t} ¬gv r | stu σ        = σ
lem-a5 {t} ¬gv r | val v        = r ↯ W.v→nf (ov→wv v)
lem-a5 {t} ¬gv r | red (_ , r′) with W.⟹-det r (or→wr r′)
lem-a5 {t} ¬gv r | red (u , r′) | refl = help-0 u ↯ ¬gv


----------------------------------------------------------------------------------------------------
--
-- Towards Proposition A.2. (right-to-left)
--
-- TODO: Clean this up
--
-- find first reduction that goes from `u` to `w` such that `w` contains `wrong`.
-- `w→o u` will be our result
-- as long as we started with a `t` that did not contain `wrong` anywhere,
-- all terms up to and including `u` will not contain `wrong` anywhere,
-- because the only rules that produce `wrong` are `*Wrong` rules;
-- therefore we can translate all reductions up to the one that involves `u`.

-- Step 0

find-0 : ∀ {t} → GoodTerm t → W[ t ⟹* wrong ] → (∃ λ u → GoodTerm u × Σ W[ t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-0 {t} () []
find-0 {t} gt (r ∷⟨ u ⟩ rs)        with good? u
... | no ¬gu                       = t , gt , ([] , []) , u , ¬gu , r
... | yes gu                       with find-0 gu rs
... | u′ , gu′ , (rs′ , grs′) , vx = u′ , gu′ , ((r ∷ rs′) , (gu ∷ grs′)) , vx

-- Step 1

find-1 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → GoodTerm u × Σ W[ o→w t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-1 {t} rs = find-0 (help-0 t) rs

help-1a : ∀ {t u} → (gt : GoodTerm t) → W[ t ⟹ u ] ≡ W[ o→w (w→o gt) ⟹ u ]
help-1a gt rewrite help-1 gt = refl

help-1b : ∀ {t u} → (gu : GoodTerm u) → W[ t ⟹* u ] ≡ W[ t ⟹* o→w (w→o gu) ]
help-1b gu rewrite help-1 gu = refl

help-1c : ∀ {t u} {rs : W[ o→w t ⟹* u ]} → (gu : GoodTerm u) → GoodReds rs ≡ GoodReds (coerce rs (help-1b gu))
help-1c gu rewrite help-1 gu = refl

-- Step 2

find-2 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → Σ W[ o→w t ⟹* o→w u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ o→w u ⟹ v ])
find-2 {t} rs                             with find-1 {t} rs
... | u , gu , (rs′ , grs′) , v , ¬gv , r = w→o gu , (coerce rs′ (help-1b gu) , coerce grs′ (help-1c {t} gu)) , v , ¬gv , (coerce r (help-1a gu))

-- Step 3

find-3 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → O.Stuck u × Σ W[ o→w t ⟹* o→w u ] GoodReds)
find-3 {t} rs                        with find-2 {t} rs
... | u , (rs′ , grs′) , v , ¬gv , r = u , lem-a5 ¬gv r , (rs′ , grs′)

help-3b : ∀ {t u} → (gt : GoodTerm (o→w t)) (gu : GoodTerm (o→w u)) → O[ w→o gt ⟹* w→o gu ] → O[ t ⟹* u ]
help-3b {t} {u} gt gu rs rewrite help-3a {t} gt | help-3a {u} gu = rs

help-3c : ∀ {t u} → (rs : W[ o→w t ⟹* o→w u ]) → GoodReds rs → O[ t ⟹* u ]
help-3c {t} {u} rs grs with help-0 t | help-0 u
... | gt | gu          = help-3b gt gu (wrs→ors gt gu rs grs)


----------------------------------------------------------------------------------------------------
--
-- Proposition A.2.
-- “For all original terms `t`, (`O[ t ⟹* u ]` where `u` is stuck) iff (`W[ t ⟹* wrong ]`).”

prop-a2-1 : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⟹* u ]) → W[ o→w t ⟹* wrong ]
prop-a2-1 (u , σ , [])     = lem-a4 σ
prop-a2-1 (u , σ , r ∷ rs) = or→wr r ∷ prop-a2-1 (u , σ , rs)

prop-a2-2 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → O.Stuck u × O[ t ⟹* u ])
prop-a2-2 {t} rs           with find-3 {t} rs
... | u , σᵤ , (rs′ , grs′) = u , σᵤ , help-3c rs′ grs′

prop-a2 : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⟹* u ]) ↔ W[ o→w t ⟹* wrong ]
prop-a2 = prop-a2-1 , prop-a2-2
