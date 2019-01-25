module Chapter3a where

open import Chapter3 public

open module O = NumbersAndBooleansGetStuck
  renaming (_⟹_ to O[_⟹_] ; _⟹*_ to O[_⟹*_] ; _⟹*′_ to O[_⟹*′_])

open module W = NumbersAndBooleansGoWrong
  renaming (_⟹_ to W[_⟹_] ; _⟹*_ to W[_⟹*_] ; _⟹*′_ to W[_⟹*′_])


pattern _∷⟨_⟩_ r t rs = _∷_ {_} {t} {_} r rs
pattern _∷ʳ′⟨_⟩_ rs t r = _∷ʳ′_ {_} {t} {_} rs r


----------------------------------------------------------------------------------------------------
--
-- Easy part


-- Equipment

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

-- NOTE: Not used
ors→wrs : ∀ {t u} → O[ t ⟹* u ] → W[ o→w t ⟹* o→w u ]
ors→wrs []       = []
ors→wrs (r ∷ rs) = or→wr r ∷ ors→wrs rs


-- Lemma A.4.

lem-a4 : ∀ {t} → Stuck t → W[ o→w t ⟹* wrong ]
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


-- Proposition A.2. (part 1)

prop-a21 : ∀ {t} → (∃ λ u → Stuck u × O[ t ⟹* u ]) → W[ o→w t ⟹* wrong ]
prop-a21 (u , σ , [])     = lem-a4 σ
prop-a21 (u , σ , r ∷ rs) = or→wr r ∷ prop-a21 (u , σ , rs)


----------------------------------------------------------------------------------------------------
--
-- Prelude to hard part


-- Equipment based on ¬ BadTerm

module ¬BadTermKit where
  w→o : ∀ {t} → ¬ W.BadTerm t → O.Term
  w→o {wrong}                 ¬bt = [] ↯ ¬bt
  w→o {true}                  ¬bt = true
  w→o {false}                 ¬bt = false
  w→o {zero}                  ¬bt = zero
  w→o {suc t}                 ¬bt = suc (w→o (undo suc ¬bt))
  w→o {pred t}                ¬bt = pred (w→o (undo pred ¬bt))
  w→o {iszero t}              ¬bt = iszero (w→o (undo iszero ¬bt))
  w→o {if t₁ then t₂ else t₃} ¬bt = if (w→o (undo if₁ ¬bt)) then (w→o (undo if₂ ¬bt)) else (w→o (undo if₃ ¬bt))

  wnv→onv : ∀ {t} → (¬bt : ¬ W.BadTerm t) → W.NumericValue t → O.NumericValue (w→o ¬bt)
  wnv→onv ¬bt zero     = zero
  wnv→onv ¬bt (suc nv) = suc (wnv→onv (undo suc ¬bt) nv)

  wv→ov : ∀ {t} → (¬bt : ¬ W.BadTerm t) → W.Value t → O.Value (w→o ¬bt)
  wv→ov ¬bt wrong    = [] ↯ ¬bt
  wv→ov ¬bt true     = true
  wv→ov ¬bt false    = false
  wv→ov ¬bt (num nv) = num (wnv→onv ¬bt nv)

  -- NOTE: Problematic
  -- wr→or : ∀ {t u} → (¬bt : ¬ W.W.BadTerm t) (¬bu : ¬ W.W.BadTerm u) → W[ t ⟹ u ] → O[ w→o ¬bt ⟹ w→o ¬bu ]
  -- wr→or ¬bt ¬bu (r-sucWrong bn)    = [] ↯ ¬bu
  -- wr→or ¬bt ¬bu (r-suc r)          = r-suc (wr→or (undo suc ¬bt) (undo suc ¬bu) r)
  -- wr→or ¬bt ¬bu (r-predWrong bn)   = [] ↯ ¬bu
  -- wr→or ¬bt ¬bu r-predZero         = r-predZero
  -- wr→or ¬bt ¬bu (r-predSuc nv)     = {!!}
  -- wr→or ¬bt ¬bu (r-pred r)         = r-pred (wr→or (undo pred ¬bt) (undo pred ¬bu) r)
  -- wr→or ¬bt ¬bu (r-iszeroWrong bn) = [] ↯ ¬bu
  -- wr→or ¬bt ¬bu r-iszeroZero       = r-iszeroZero
  -- wr→or ¬bt ¬bu (r-iszeroSuc nv)   = r-iszeroSuc (wnv→onv (undo suc (undo iszero ¬bt)) nv)
  -- wr→or ¬bt ¬bu (r-iszero r)       = r-iszero (wr→or (undo iszero ¬bt) (undo iszero ¬bu) r)
  -- wr→or ¬bt ¬bu (r-ifWrong bb)     = [] ↯ ¬bu
  -- wr→or ¬bt ¬bu r-ifTrue           = {!!}
  -- wr→or ¬bt ¬bu r-ifFalse          = {!!}
  -- wr→or ¬bt ¬bu (r-if r)           = {!!}

  lem-1 : ∀ {u} → ¬ W.BadTerm u → (∃ λ t → o→w t ≡ u)
  lem-1 {wrong}                 ¬bu       = [] ↯ ¬bu
  lem-1 {true}                  ¬bu       = true , refl
  lem-1 {false}                 ¬bu       = false , refl
  lem-1 {zero}                  ¬bu       = zero , refl
  lem-1 {suc u}                 ¬bu       with lem-1 (undo suc ¬bu)
  ... | t , refl                          = suc t , refl
  lem-1 {pred u}                ¬bu       with lem-1 (undo pred ¬bu)
  ... | t , refl                          = pred t , refl
  lem-1 {iszero u}              ¬bu       with lem-1 (undo iszero ¬bu)
  ... | t , refl                          = iszero t , refl
  lem-1 {if u₁ then u₂ else u₃} ¬bu       with lem-1 (undo if₁ ¬bu) | lem-1 (undo if₂ ¬bu) | lem-1 (undo if₃ ¬bu)
  ... | t₁ , refl | t₂ , refl | t₃ , refl = if t₁ then t₂ else t₃ , refl


-- Equipment based on ¬ BadTerm′

module ¬BadTermKit′ where
  w→o : ∀ {t} → ¬ W.BadTerm′ t → O.Term
  w→o {wrong}                 ¬bt = []′ ↯ ¬bt
  w→o {true}                  ¬bt = true
  w→o {false}                 ¬bt = false
  w→o {zero}                  ¬bt = zero
  w→o {suc t}                 ¬bt = suc (w→o (undo′ suc ¬bt))
  w→o {pred t}                ¬bt = pred (w→o (undo′ pred ¬bt))
  w→o {iszero t}              ¬bt = iszero (w→o (undo′ iszero ¬bt))
  w→o {if t₁ then t₂ else t₃} ¬bt = if (w→o (undo′ if₁ ¬bt)) then (w→o (undo′ if₂ ¬bt)) else (w→o (undo′ if₃ ¬bt))

  wnv→onv : ∀ {t} → (¬bt : ¬ W.BadTerm′ t) → W.NumericValue t → O.NumericValue (w→o ¬bt)
  wnv→onv ¬bt zero     = zero
  wnv→onv ¬bt (suc nv) = suc (wnv→onv (undo′ suc ¬bt) nv)

  wv→ov : ∀ {t} → (¬bt : ¬ W.BadTerm′ t) → W.Value t → O.Value (w→o ¬bt)
  wv→ov ¬bt wrong    = []′ ↯ ¬bt
  wv→ov ¬bt true     = true
  wv→ov ¬bt false    = false
  wv→ov ¬bt (num nv) = num (wnv→onv ¬bt nv)

  -- NOTE: Still problematic
  -- wr→or : ∀ {t u} → (¬bt : ¬ W.BadTerm′ t) (¬bu : ¬ W.BadTerm′ u) → W[ t ⟹ u ] → O[ w→o ¬bt ⟹ w→o ¬bu ]
  -- wr→or ¬bt ¬bu (r-sucWrong bn)    = []′ ↯ ¬bu
  -- wr→or ¬bt ¬bu (r-suc r)          = r-suc (wr→or (undo′ suc ¬bt) (undo′ suc ¬bu) r)
  -- wr→or ¬bt ¬bu (r-predWrong bn)   = []′ ↯ ¬bu
  -- wr→or ¬bt ¬bu r-predZero         = r-predZero
  -- wr→or ¬bt ¬bu (r-predSuc nv)     = {!!}
  -- wr→or ¬bt ¬bu (r-pred r)         = r-pred (wr→or (undo′ pred ¬bt) (undo′ pred ¬bu) r)
  -- wr→or ¬bt ¬bu (r-iszeroWrong bn) = []′ ↯ ¬bu
  -- wr→or ¬bt ¬bu r-iszeroZero       = r-iszeroZero
  -- wr→or ¬bt ¬bu (r-iszeroSuc nv)   = r-iszeroSuc (wnv→onv (undo′ suc (undo′ iszero ¬bt)) nv)
  -- wr→or ¬bt ¬bu (r-iszero r)       = r-iszero (wr→or (undo′ iszero ¬bt) (undo′ iszero ¬bu) r)
  -- wr→or ¬bt ¬bu (r-ifWrong bb)     = []′ ↯ ¬bu
  -- wr→or ¬bt ¬bu r-ifTrue           = {!!}
  -- wr→or ¬bt ¬bu r-ifFalse          = {!!}
  -- wr→or ¬bt ¬bu (r-if r)           = {!!}

  lem-1 : ∀ {u} → ¬ W.BadTerm′ u → (∃ λ t → o→w t ≡ u)
  lem-1 {wrong}                 ¬bu       = []′ ↯ ¬bu
  lem-1 {true}                  ¬bu       = true , refl
  lem-1 {false}                 ¬bu       = false , refl
  lem-1 {zero}                  ¬bu       = zero , refl
  lem-1 {suc u}                 ¬bu       with lem-1 (undo′ suc ¬bu)
  ... | t , refl                          = suc t , refl
  lem-1 {pred u}                ¬bu       with lem-1 (undo′ pred ¬bu)
  ... | t , refl                          = pred t , refl
  lem-1 {iszero u}              ¬bu       with lem-1 (undo′ iszero ¬bu)
  ... | t , refl                          = iszero t , refl
  lem-1 {if u₁ then u₂ else u₃} ¬bu       with lem-1 (undo′ if₁ ¬bu) | lem-1 (undo′ if₂ ¬bu) | lem-1 (undo′ if₃ ¬bu)
  ... | t₁ , refl | t₂ , refl | t₃ , refl = if t₁ then t₂ else t₃ , refl


-- Equipment based on ¬ BadTermI

module ¬BadTermKitI where
  w→o : ∀ {t} → ¬ W.BadTermI t → O.Term
  w→o {wrong}                 ¬bt = wrong ↯ ¬bt
  w→o {true}                  ¬bt = true
  w→o {false}                 ¬bt = false
  w→o {zero}                  ¬bt = zero
  w→o {suc t}                 ¬bt = suc (w→o (undoI suc ¬bt))
  w→o {pred t}                ¬bt = pred (w→o (undoI pred ¬bt))
  w→o {iszero t}              ¬bt = iszero (w→o (undoI iszero ¬bt))
  w→o {if t₁ then t₂ else t₃} ¬bt = if (w→o (undoI if₁ ¬bt)) then (w→o (undoI if₂ ¬bt)) else (w→o (undoI if₃ ¬bt))

  wnv→onv : ∀ {t} → (¬bt : ¬ W.BadTermI t) → W.NumericValue t → O.NumericValue (w→o ¬bt)
  wnv→onv ¬bt zero     = zero
  wnv→onv ¬bt (suc nv) = suc (wnv→onv (undoI suc ¬bt) nv)

  wv→ov : ∀ {t} → (¬bt : ¬ W.BadTermI t) → W.Value t → O.Value (w→o ¬bt)
  wv→ov ¬bt wrong    = wrong ↯ ¬bt
  wv→ov ¬bt true     = true
  wv→ov ¬bt false    = false
  wv→ov ¬bt (num nv) = num (wnv→onv ¬bt nv)

  -- NOTE: Also problematic
  -- wr→or : ∀ {t u} → (¬bt : ¬ W.BadTermI t) (¬bu : ¬ W.BadTermI u) → W[ t ⟹ u ] → O[ w→o ¬bt ⟹ w→o ¬bu ]
  -- wr→or ¬bt ¬bu (r-sucWrong bn)    = wrong ↯ ¬bu
  -- wr→or ¬bt ¬bu (r-suc r)          = r-suc (wr→or (undoI suc ¬bt) (undoI suc ¬bu) r)
  -- wr→or ¬bt ¬bu (r-predWrong bn)   = wrong ↯ ¬bu
  -- wr→or ¬bt ¬bu r-predZero         = r-predZero
  -- wr→or ¬bt ¬bu (r-predSuc nv)     = {!!}
  -- wr→or ¬bt ¬bu (r-pred r)         = r-pred (wr→or (undoI pred ¬bt) (undoI pred ¬bu) r)
  -- wr→or ¬bt ¬bu (r-iszeroWrong bn) = wrong ↯ ¬bu
  -- wr→or ¬bt ¬bu r-iszeroZero       = r-iszeroZero
  -- wr→or ¬bt ¬bu (r-iszeroSuc nv)   = r-iszeroSuc (wnv→onv (undoI suc (undoI iszero ¬bt)) nv)
  -- wr→or ¬bt ¬bu (r-iszero r)       = r-iszero (wr→or (undoI iszero ¬bt) (undoI iszero ¬bu) r)
  -- wr→or ¬bt ¬bu (r-ifWrong bb)     = wrong ↯ ¬bu
  -- wr→or ¬bt ¬bu r-ifTrue           = {!!}
  -- wr→or ¬bt ¬bu r-ifFalse          = {!!}
  -- wr→or ¬bt ¬bu (r-if r)           = {!!}

  lem-1 : ∀ {u} → ¬ W.BadTermI u → (∃ λ t → o→w t ≡ u)
  lem-1 {wrong}                 ¬bu       = wrong ↯ ¬bu
  lem-1 {true}                  ¬bu       = true , refl
  lem-1 {false}                 ¬bu       = false , refl
  lem-1 {zero}                  ¬bu       = zero , refl
  lem-1 {suc u}                 ¬bu       with lem-1 (undoI suc ¬bu)
  ... | t , refl                          = suc t , refl
  lem-1 {pred u}                ¬bu       with lem-1 (undoI pred ¬bu)
  ... | t , refl                          = pred t , refl
  lem-1 {iszero u}              ¬bu       with lem-1 (undoI iszero ¬bu)
  ... | t , refl                          = iszero t , refl
  lem-1 {if u₁ then u₂ else u₃} ¬bu       with lem-1 (undoI if₁ ¬bu) | lem-1 (undoI if₂ ¬bu) | lem-1 (undoI if₃ ¬bu)
  ... | t₁ , refl | t₂ , refl | t₃ , refl = if t₁ then t₂ else t₃ , refl


-- Equipment based on GoodTerm

module _ where
  w→o : ∀ {t} → W.GoodTerm t → O.Term
  w→o true                       = true
  w→o false                      = false
  w→o zero                       = zero
  w→o (suc gt)                   = suc (w→o gt)
  w→o (pred gt)                  = pred (w→o gt)
  w→o (iszero gt)                = iszero (w→o gt)
  w→o (if gt₁ then gt₂ else gt₃) = if (w→o gt₁) then (w→o gt₂) else (w→o gt₃)

  wnv→onv : ∀ {t} → (gt : W.GoodTerm t) → W.NumericValue t → O.NumericValue (w→o gt)
  wnv→onv zero     zero     = zero
  wnv→onv (suc gt) (suc nv) = suc (wnv→onv gt nv)

  wv→ov : ∀ {t} → (gt : W.GoodTerm t) → W.Value t → O.Value (w→o gt)
  wv→ov true                       true           = true
  wv→ov true                       (num ())
  wv→ov false                      false          = false
  wv→ov false                      (num ())
  wv→ov zero                       (num zero)     = num zero
  wv→ov (suc gt)                   (num (suc nv)) = num (suc (wnv→onv gt nv))
  wv→ov (pred gt)                  (num ())
  wv→ov (iszero gt)                (num ())
  wv→ov (if gt₁ then gt₂ else gt₃) (num ())

  wr→or : ∀ {t u} → (gt : W.GoodTerm t) (gu : W.GoodTerm u) → W[ t ⟹ u ] → O[ w→o gt ⟹ w→o gu ]
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

  lem-1 : ∀ {u} → W.GoodTerm u → (∃ λ t → u ≡ o→w t)
  lem-1 true                              = true , refl
  lem-1 false                             = false , refl
  lem-1 zero                              = zero , refl
  lem-1 (suc gu)                          with lem-1 gu
  ... | t , refl                          = suc t , refl
  lem-1 (pred gu)                         with lem-1 gu
  ... | t , refl                          = pred t , refl
  lem-1 (iszero gu)                       with lem-1 gu
  ... | t , refl                          = iszero t , refl
  lem-1 (if gu₁ then gu₂ else gu₃)        with lem-1 gu₁ | lem-1 gu₂ | lem-1 gu₃
  ... | t₁ , refl | t₂ , refl | t₃ , refl = if t₁ then t₂ else t₃ , refl

  ¬gt-redo : ∀ {t u} → t W.∈ u → ¬ W.GoodTerm t → ¬ W.GoodTerm u
  ¬gt-redo suc    ¬gt  = λ where (suc gt) → gt ↯ ¬gt
  ¬gt-redo pred   ¬gt  = λ where (pred gt) → gt ↯ ¬gt
  ¬gt-redo iszero ¬gt  = λ where (iszero gt) → gt ↯ ¬gt
  ¬gt-redo if₁    ¬gt₁ = λ where (if gt₁ then gt₂ else gt₃) → gt₁ ↯ ¬gt₁
  ¬gt-redo if₂    ¬gt₂ = λ where (if gt₁ then gt₂ else gt₃) → gt₂ ↯ ¬gt₂
  ¬gt-redo if₃    ¬gt₃ = λ where (if gt₁ then gt₂ else gt₃) → gt₃ ↯ ¬gt₃

  ¬¬gt-undo : ∀ {t u} → t W.∈ u → ¬ ¬ W.GoodTerm u → ¬ ¬ W.GoodTerm t
  ¬¬gt-undo suc    ¬¬gu = λ ¬gt  → ¬gt-redo suc ¬gt ↯ ¬¬gu
  ¬¬gt-undo pred   ¬¬gu = λ ¬gt  → ¬gt-redo pred ¬gt ↯ ¬¬gu
  ¬¬gt-undo iszero ¬¬gu = λ ¬gt  → ¬gt-redo iszero ¬gt ↯ ¬¬gu
  ¬¬gt-undo if₁    ¬¬gu = λ ¬gt₁ → ¬gt-redo if₁ ¬gt₁ ↯ ¬¬gu
  ¬¬gt-undo if₂    ¬¬gu = λ ¬gt₂ → ¬gt-redo if₂ ¬gt₂ ↯ ¬¬gu
  ¬¬gt-undo if₃    ¬¬gu = λ ¬gt₃ → ¬gt-redo if₃ ¬gt₃ ↯ ¬¬gu

  ¬¬gt→gt : ∀ {t} → ¬ ¬ W.GoodTerm t → W.GoodTerm t
  ¬¬gt→gt {wrong}                 ¬¬gt = (λ _ → (λ ()) ↯ ¬¬gt) ↯ ¬¬gt
  ¬¬gt→gt {true}                  ¬¬gt = true
  ¬¬gt→gt {false}                 ¬¬gt = false
  ¬¬gt→gt {zero}                  ¬¬gt = zero
  ¬¬gt→gt {suc t}                 ¬¬gt = suc (¬¬gt→gt {t} (¬¬gt-undo suc ¬¬gt))
  ¬¬gt→gt {pred t}                ¬¬gt = pred (¬¬gt→gt {t} (¬¬gt-undo pred ¬¬gt))
  ¬¬gt→gt {iszero t}              ¬¬gt = iszero (¬¬gt→gt {t} (¬¬gt-undo iszero ¬¬gt))
  ¬¬gt→gt {if t₁ then t₂ else t₃} ¬¬gt = if (¬¬gt→gt {t₁} (¬¬gt-undo if₁ ¬¬gt))
                                          then (¬¬gt→gt {t₂} (¬¬gt-undo if₂ ¬¬gt))
                                          else (¬¬gt→gt {t₃} (¬¬gt-undo if₃ ¬¬gt))


module OKit where
  _∈?_ : Decidable O._∈_
  s ∈? true                            = no λ ()
  s ∈? false                           = no λ ()
  s ∈? zero                            = no λ ()
  s ∈? suc t                           with s O.≟ t
  ... | yes refl                       = yes suc
  ... | no s≢t                         = no λ where suc → refl ↯ s≢t
  s ∈? pred t                          with s O.≟ t
  ... | yes refl                       = yes pred
  ... | no s≢t                         = no λ where pred → refl ↯ s≢t
  s ∈? iszero t                        with s O.≟ t
  ... | yes refl                       = yes iszero
  ... | no s≢t                         = no λ where iszero → refl ↯ s≢t
  s ∈? if t₁ then t₂ else t₃           with s O.≟ t₁ | s O.≟ t₂ | s O.≟ t₃
  ... | yes refl | _        | _        = yes if₁
  ... | no s≢t₁  | yes refl | _        = yes if₂
  ... | no s≢t₁  | no s≢t₂  | yes refl = yes if₃
  ... | no s≢t₁  | no s≢t₂  | no s≢t₃  = no λ where if₁ → refl ↯ s≢t₁
                                                    if₂ → refl ↯ s≢t₂
                                                    if₃ → refl ↯ s≢t₃

  _∈*?′_ : Decidable O._∈*′_
  s ∈*?′ t with s O.≟ t
  ...                            | yes refl = yes []′
  (s ∈*?′ true)                  | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ false)                 | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ zero)                  | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ suc u)                 | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ suc)
  ... | no ¬p                               = no λ where []′         → refl ↯ s≢t
                                                         (p ∷ʳ′ suc) → p ↯ ¬p
  (s ∈*?′ pred u)                | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ pred)
  ... | no ¬p                               = no λ where []′          → refl ↯ s≢t
                                                         (p ∷ʳ′ pred) → p ↯ ¬p
  (s ∈*?′ iszero u)              | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ iszero)
  ... | no ¬p                               = no λ where []′            → refl ↯ s≢t
                                                         (p ∷ʳ′ iszero) → p ↯ ¬p
  (s ∈*?′ if u₁ then u₂ else u₃) | no s≢t   with s ∈*?′ u₁ | s ∈*?′ u₂ | s ∈*?′ u₃
  ... | yes p₁ | _      | _                 = yes (p₁ ∷ʳ′ if₁)
  ... | no ¬p₁ | yes p₂ | _                 = yes (p₂ ∷ʳ′ if₂)
  ... | no ¬p₁ | no ¬p₂ | yes p₃            = yes (p₃ ∷ʳ′ if₃)
  ... | no ¬p₁ | no ¬p₂ | no ¬p₃            = no λ where []′          → refl ↯ s≢t
                                                         (p₁ ∷ʳ′ if₁) → p₁ ↯ ¬p₁
                                                         (p₂ ∷ʳ′ if₂) → p₂ ↯ ¬p₂
                                                         (p₃ ∷ʳ′ if₃) → p₃ ↯ ¬p₃


module _ where
  _∈?_ : Decidable W._∈_
  s ∈? wrong                           = no λ ()
  s ∈? true                            = no λ ()
  s ∈? false                           = no λ ()
  s ∈? zero                            = no λ ()
  s ∈? suc t                           with s W.≟ t
  ... | yes refl                       = yes suc
  ... | no s≢t                         = no λ where suc → refl ↯ s≢t
  s ∈? pred t                          with s W.≟ t
  ... | yes refl                       = yes pred
  ... | no s≢t                         = no λ where pred → refl ↯ s≢t
  s ∈? iszero t                        with s W.≟ t
  ... | yes refl                       = yes iszero
  ... | no s≢t                         = no λ where iszero → refl ↯ s≢t
  s ∈? if t₁ then t₂ else t₃           with s W.≟ t₁ | s W.≟ t₂ | s W.≟ t₃
  ... | yes refl | _        | _        = yes if₁
  ... | no s≢t₁  | yes refl | _        = yes if₂
  ... | no s≢t₁  | no s≢t₂  | yes refl = yes if₃
  ... | no s≢t₁  | no s≢t₂  | no s≢t₃  = no λ where if₁ → refl ↯ s≢t₁
                                                    if₂ → refl ↯ s≢t₂
                                                    if₃ → refl ↯ s≢t₃

  _∈*?′_ : Decidable W._∈*′_
  s ∈*?′ t with s W.≟ t
  ...                            | yes refl = yes []′
  (s ∈*?′ wrong)                 | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ true)                  | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ false)                 | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ zero)                  | no s≢t   = no λ where []′ → refl ↯ s≢t
                                                         (_ ∷ʳ′ ())
  (s ∈*?′ suc u)                 | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ suc)
  ... | no ¬p                               = no λ where []′         → refl ↯ s≢t
                                                         (p ∷ʳ′ suc) → p ↯ ¬p
  (s ∈*?′ pred u)                | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ pred)
  ... | no ¬p                               = no λ where []′          → refl ↯ s≢t
                                                         (p ∷ʳ′ pred) → p ↯ ¬p
  (s ∈*?′ iszero u)              | no s≢t   with s ∈*?′ u
  ... | yes p                               = yes (p ∷ʳ′ iszero)
  ... | no ¬p                               = no λ where []′            → refl ↯ s≢t
                                                         (p ∷ʳ′ iszero) → p ↯ ¬p
  (s ∈*?′ if u₁ then u₂ else u₃) | no s≢t   with s ∈*?′ u₁ | s ∈*?′ u₂ | s ∈*?′ u₃
  ... | yes p₁ | _      | _                 = yes (p₁ ∷ʳ′ if₁)
  ... | no ¬p₁ | yes p₂ | _                 = yes (p₂ ∷ʳ′ if₂)
  ... | no ¬p₁ | no ¬p₂ | yes p₃            = yes (p₃ ∷ʳ′ if₃)
  ... | no ¬p₁ | no ¬p₂ | no ¬p₃            = no λ where []′          → refl ↯ s≢t
                                                         (p₁ ∷ʳ′ if₁) → p₁ ↯ ¬p₁
                                                         (p₂ ∷ʳ′ if₂) → p₂ ↯ ¬p₂
                                                         (p₃ ∷ʳ′ if₃) → p₃ ↯ ¬p₃


module _ where
  ¬bt→gt : ∀ {t} → ¬ W.BadTerm t → W.GoodTerm t
  ¬bt→gt {wrong}                 ¬bt = [] ↯ ¬bt
  ¬bt→gt {true}                  ¬bt = true
  ¬bt→gt {false}                 ¬bt = false
  ¬bt→gt {zero}                  ¬bt = zero
  ¬bt→gt {suc t}                 ¬bt = suc (¬bt→gt (undo suc ¬bt))
  ¬bt→gt {pred t}                ¬bt = pred (¬bt→gt (undo pred ¬bt))
  ¬bt→gt {iszero t}              ¬bt = iszero (¬bt→gt (undo iszero ¬bt))
  ¬bt→gt {if t₁ then t₂ else t₃} ¬bt = if (¬bt→gt (undo if₁ ¬bt))
                                        then (¬bt→gt (undo if₂ ¬bt))
                                        else (¬bt→gt (undo if₃ ¬bt))

  ¬bt→gt′ : ∀ {t} → ¬ W.BadTerm′ t → W.GoodTerm t
  ¬bt→gt′ {wrong}                 ¬bt = []′ ↯ ¬bt
  ¬bt→gt′ {true}                  ¬bt = true
  ¬bt→gt′ {false}                 ¬bt = false
  ¬bt→gt′ {zero}                  ¬bt = zero
  ¬bt→gt′ {suc t}                 ¬bt = suc (¬bt→gt′ (undo′ suc ¬bt))
  ¬bt→gt′ {pred t}                ¬bt = pred (¬bt→gt′ (undo′ pred ¬bt))
  ¬bt→gt′ {iszero t}              ¬bt = iszero (¬bt→gt′ (undo′ iszero ¬bt))
  ¬bt→gt′ {if t₁ then t₂ else t₃} ¬bt = if (¬bt→gt′ (undo′ if₁ ¬bt))
                                         then (¬bt→gt′ (undo′ if₂ ¬bt))
                                         else (¬bt→gt′ (undo′ if₃ ¬bt))


  -- NOTE: Problematic
  -- gt→¬bt : ∀ {t} → W.GoodTerm t → ¬ W.BadTerm t
  -- gt→¬bt true                       = λ x → {!!}
  -- gt→¬bt false                      = {!!}
  -- gt→¬bt zero                       = {!!}
  -- gt→¬bt (suc gt)                   = {!!}
  -- gt→¬bt (pred gt)                  = {!!}
  -- gt→¬bt (iszero gt)                = {!!}
  -- gt→¬bt (if gt₁ then gt₂ else gt₃) = {!!}

  gt→¬bt′ : ∀ {t} → W.GoodTerm t → ¬ W.BadTerm′ t
  gt→¬bt′ true                       = λ where (_ ∷ʳ′ ())
  gt→¬bt′ false                      = λ where (_ ∷ʳ′ ())
  gt→¬bt′ zero                       = λ where (_ ∷ʳ′ ())
  gt→¬bt′ (suc gt)                   = λ where (bt ∷ʳ′ suc) → bt ↯ gt→¬bt′ gt
  gt→¬bt′ (pred gt)                  = λ where (bt ∷ʳ′ pred) → bt ↯ gt→¬bt′ gt
  gt→¬bt′ (iszero gt)                = λ where (bt ∷ʳ′ iszero) → bt ↯ gt→¬bt′ gt
  gt→¬bt′ (if gt₁ then gt₂ else gt₃) = λ where -- NOTE: Layout bug here
    (bt₁ ∷ʳ′ if₁) → bt₁ ↯ gt→¬bt′ gt₁
    (bt₂ ∷ʳ′ if₂) → bt₂ ↯ gt→¬bt′ gt₂
    (bt₃ ∷ʳ′ if₃) → bt₃ ↯ gt→¬bt′ gt₃


  -- NOTE: Problematic
  -- bt→¬gt : ∀ {t} → W.BadTerm t → ¬ W.GoodTerm t
  -- bt→¬gt {wrong}                 bt = λ ()
  -- bt→¬gt {true}                  bt = {!!}
  -- bt→¬gt {false}                 bt = {!!}
  -- bt→¬gt {zero}                  bt = {!!}
  -- bt→¬gt {suc t}                 bt = {!!}
  -- bt→¬gt {pred t}                bt = {!!}
  -- bt→¬gt {iszero t}              bt = {!!}
  -- bt→¬gt {if t₁ then t₂ else t₃} bt = {!!}

  bt→¬gt′ : ∀ {t} → W.BadTerm′ t → ¬ W.GoodTerm t
  bt→¬gt′ {wrong}                 _                = λ ()
  bt→¬gt′ {true}                  (_   ∷ʳ′ ())
  bt→¬gt′ {false}                 (_   ∷ʳ′ ())
  bt→¬gt′ {zero}                  (_   ∷ʳ′ ())
  bt→¬gt′ {suc t}                 (bt  ∷ʳ′ suc)    = λ where (suc gt) → gt ↯ bt→¬gt′ bt
  bt→¬gt′ {pred t}                (bt  ∷ʳ′ pred)   = λ where (pred gt) → gt ↯ bt→¬gt′ bt
  bt→¬gt′ {iszero t}              (bt  ∷ʳ′ iszero) = λ where (iszero gt) → gt ↯ bt→¬gt′ bt
  bt→¬gt′ {if t₁ then t₂ else t₃} (bt₁ ∷ʳ′ if₁)    = λ where (if gt₁ then gt₂ else gt₃) → gt₁ ↯ bt→¬gt′ bt₁
  bt→¬gt′ {if t₁ then t₂ else t₃} (bt₂ ∷ʳ′ if₂)    = λ where (if gt₁ then gt₂ else gt₃) → gt₂ ↯ bt→¬gt′ bt₂
  bt→¬gt′ {if t₁ then t₂ else t₃} (bt₃ ∷ʳ′ if₃)    = λ where (if gt₁ then gt₂ else gt₃) → gt₃ ↯ bt→¬gt′ bt₃


  bad?′ : ∀ t → Dec (W.BadTerm′ t)
  bad?′ t = wrong ∈*?′ t

  good? : ∀ t → Dec (W.GoodTerm t)
  good? t with bad?′ t
  ... | yes bt = no λ gt → bt ↯ gt→¬bt′ gt
  ... | no ¬bt = yes (¬bt→gt′ ¬bt)


  -- NOTE: Is there no easier way?
  ¬gt→bt′ : ∀ {t} → ¬ W.GoodTerm t → W.BadTerm′ t
  ¬gt→bt′ {wrong}                 ¬gt = []′
  ¬gt→bt′ {true}                  ¬gt = true ↯ ¬gt
  ¬gt→bt′ {false}                 ¬gt = false ↯ ¬gt
  ¬gt→bt′ {zero}                  ¬gt = zero ↯ ¬gt
  ¬gt→bt′ {suc t}                 ¬gt = ¬gt→bt′ (λ gt → (suc gt) ↯ ¬gt) ∷ʳ′ suc
  ¬gt→bt′ {pred t}                ¬gt = ¬gt→bt′ (λ gt → (pred gt) ↯ ¬gt) ∷ʳ′ pred
  ¬gt→bt′ {iszero t}              ¬gt = ¬gt→bt′ (λ gt → (iszero gt) ↯ ¬gt) ∷ʳ′ iszero
  ¬gt→bt′ {if t₁ then t₂ else t₃} ¬gt with good? t₁ | good? t₂ | good? t₃
  ... | no ¬gt₁ | _       | _          = ¬gt→bt′ (λ gt₁ → gt₁ ↯ ¬gt₁) ∷ʳ′ if₁
  ... | yes gt₁ | no ¬gt₂ | _          = ¬gt→bt′ (λ gt₂ → gt₂ ↯ ¬gt₂) ∷ʳ′ if₂
  ... | yes gt₁ | yes gt₂ | no ¬gt₃    = ¬gt→bt′ (λ gt₃ → gt₃ ↯ ¬gt₃) ∷ʳ′ if₃
  ... | yes gt₁ | yes gt₂ | yes gt₃    = if gt₁ then gt₂ else gt₃ ↯ ¬gt


-- NOTE: Continued in Chapter3b.agda




{-
  data 0Hole : Pred₀ W.Term where
    wrong : 0Hole wrong
    true  : 0Hole true
    false : 0Hole false
    zero  : 0Hole zero

  lem-0hole : ∀ {s t} → 0Hole t → ¬ (s W.∈ t)
  lem-0hole wrong = λ ()
  lem-0hole true  = λ ()
  lem-0hole false = λ ()
  lem-0hole zero  = λ ()

  lem-0hole* : ∀ {s t} → s ≢ t → 0Hole t → ¬ (s W.∈*′ t)
  lem-0hole* s≢t 0h = λ where
    []′       → refl ↯ s≢t
    (_ ∷ʳ′ r) → r ↯ lem-0hole 0h

  lem-0hole*′ : ∀ {s t} → 0Hole t → (s ≡ t) ⊎ ¬ (s W.∈*′ t)
  lem-0hole*′ {s} {t} 0h with s W.≟ t
  ... | yes refl  = inj₁ refl
  ... | no s≢t    = inj₂ (lem-0hole* s≢t 0h)

  lem-0hole*″ : ∀ {s t} → 0Hole t → Dec (s W.∈*′ t)
  lem-0hole*″ {s} {t} 0h with s W.≟ t
  ... | yes refl = yes []′
  ... | no s≢t   = no (lem-0hole* s≢t 0h)

  data 1Hole : Pred₀ W.Term where
    suc    : ∀ t → 1Hole (suc t)
    pred   : ∀ t → 1Hole (pred t)
    iszero : ∀ t → 1Hole (iszero t)

  lem-1hole : ∀ {s t} → 1Hole t → Dec (s W.∈ t)
  lem-1hole {s} (suc t)    with s W.≟ t
  ... | yes refl           = yes suc
  ... | no s≢t             = no λ where suc → refl ↯ s≢t
  lem-1hole {s} (pred t)   with s W.≟ t
  ... | yes refl           = yes pred
  ... | no s≢t             = no λ where pred → refl ↯ s≢t
  lem-1hole {s} (iszero t) with s W.≟ t
  ... | yes refl           = yes iszero
  ... | no s≢t             = no λ where iszero → refl ↯ s≢t

  data 3Hole : Pred₀ W.Term where
    if_then_else : ∀ t₁ t₂ t₃ → 3Hole (if t₁ then t₂ else t₃)

  lem-3hole : ∀ {s t} → 3Hole t → (s W.∈ t) ⊎ ¬ (s W.∈ t)
  lem-3hole {s} (if t₁ then t₂ else t₃) with s W.≟ t₁ | s W.≟ t₂ | s W.≟ t₃
  ... | yes refl | _        | _        = inj₁ if₁
  ... | no s≢t₁  | yes refl | _        = inj₁ if₂
  ... | no s≢t₁  | no s≢t₂  | yes refl = inj₁ if₃
  ... | no s≢t₁  | no s≢t₂  | no s≢t₃  = inj₂ λ where if₁ → refl ↯ s≢t₁
                                                      if₂ → refl ↯ s≢t₂
                                                      if₃ → refl ↯ s≢t₃

  data *Hole : Pred₀ W.Term where
    0hole : ∀ {t} → 0Hole t → *Hole t
    1hole : ∀ {t} → 1Hole t → *Hole t
    3hole : ∀ {t} → 3Hole t → *Hole t

  *hole? : ∀ t → *Hole t
  *hole? wrong                = 0hole wrong
  *hole? true                 = 0hole true
  *hole? false                = 0hole false
  *hole? zero                 = 0hole zero
  *hole? (suc _)              = 1hole (suc _)
  *hole? (pred _)             = 1hole (pred _)
  *hole? (iszero _)           = 1hole (iszero _)
  *hole? (if _ then _ else _) = 3hole (if _ then _ else _)

  _∈*′?_ : Decidable W._∈*′_
  s ∈*′? t                                          with s W.≟ t
  s ∈*′? t | yes refl                               = yes []′
  s ∈*′? t | no s≢t                                 with *hole? t
  s ∈*′? t | no s≢t | 0hole 0h                      = no (lem-0hole* s≢t 0h)
  s ∈*′? t | no s≢t | 1hole (suc u)                 with s ∈*′? u
  s ∈*′? t | no s≢t | 1hole (suc u) | yes p         = yes (p ∷ʳ′ suc)
  s ∈*′? t | no s≢t | 1hole (suc u) | no ¬p         = no λ where []′         → refl ↯ s≢t
                                                                 (p ∷ʳ′ suc) → p ↯ ¬p
  s ∈*′? t | no s≢t | 1hole (pred u)                = {!!}
  s ∈*′? t | no s≢t | 1hole (iszero u)              = {!!}
  s ∈*′? t | no s≢t | 3hole (if u₁ then u₂ else u₃) = {!!}

-}




-- -- prop-a22 : ∀ {t} → W[ o→w t ⟹*′ wrong ] → (∃ λ u → Stuck u × O[ t ⟹*′ u ])
-- -- prop-a22 {true}                  (r ∷ rs) = {!prop-a22!}
-- -- prop-a22 {false}                 (r ∷ rs) = {!!}
-- -- prop-a22 {zero}                  (r ∷ rs) = {!!}
-- -- prop-a22 {suc t}                 (r ∷ rs) = {!!}
-- -- prop-a22 {pred t}                (r ∷ rs) = {!!}
-- -- prop-a22 {iszero t}              (r ∷ rs) = {!!}
-- -- prop-a22 {if t₁ then t₂ else t₃} (r ∷ rs) = {!!}




-- {-
-- lem-a5 : ∀ {t u} → W[ o→w t ⟹ u ] → BadTerm u → Stuck t
-- lem-a5 {true}                  {u}                     ()                 _
-- lem-a5 {false}                 {u}                     ()                 _
-- lem-a5 {zero}                  {u}                     ()                 _
-- lem-a5 {suc t}                 {wrong}                 (r-sucWrong bn)    wrong       = {!!}
-- lem-a5 {suc t}                 {true}                  ()                 _
-- lem-a5 {suc t}                 {false}                 ()                 _
-- lem-a5 {suc t}                 {zero}                  ()                 _
-- lem-a5 {suc t}                 {suc u}                 (r-suc r)          (suc bu)    = {!!}
-- lem-a5 {suc t}                 {suc u}                 (r-suc r)          (pred bu)   = {!!}
-- lem-a5 {suc t}                 {pred u}                ()                 _
-- lem-a5 {suc t}                 {iszero u}              ()                 _
-- lem-a5 {suc t}                 {if u then u₁ else u₂}  ()                 _
-- lem-a5 {pred t}                {wrong}                 r                  wrong       = {!!}
-- lem-a5 {pred t}                {true}                  r                  ()
-- lem-a5 {pred t}                {false}                 r                  ()
-- lem-a5 {pred t}                {zero}                  r                  ()
-- lem-a5 {pred t}                {suc u}                 r                  (suc bu)    = {!!}
-- lem-a5 {pred t}                {suc u}                 r                  (pred bu)   = {!!}
-- lem-a5 {pred t}                {pred u}                r                  ()
-- lem-a5 {pred t}                {iszero u}              r                  (iszero bu) = {!!}
-- lem-a5 {pred t}                {if u then u₁ else u₂}  r                  (if₁ bu)    = {!!}
-- lem-a5 {pred t}                {if u then u₁ else u₂}  r                  (if₂ bu)    = {!!}
-- lem-a5 {pred t}                {if u then u₁ else u₂}  r                  (if₃ bu)    = {!!}
-- lem-a5 {iszero t}              {wrong}                 (r-iszeroWrong bn) wrong       = {!!}
-- lem-a5 {iszero t}              {true}                  r                  ()
-- lem-a5 {iszero t}              {false}                 r                  ()
-- lem-a5 {iszero t}              {zero}                  ()                 _
-- lem-a5 {iszero t}              {suc u}                 ()                 _
-- lem-a5 {iszero t}              {pred u}                ()                 _
-- lem-a5 {iszero t}              {iszero u}              (r-iszero r)       (iszero bu) = {!!}
-- lem-a5 {iszero t}              {if u then u₁ else u₂}  ()                 _
-- lem-a5 {if t₁ then t₂ else t₃} {wrong}                 r                  wrong       = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {true}                  r                  ()
-- lem-a5 {if t₁ then t₂ else t₃} {false}                 r                  ()
-- lem-a5 {if t₁ then t₂ else t₃} {zero}                  r                  ()
-- lem-a5 {if t₁ then t₂ else t₃} {suc u}                 r                  (suc bu)    = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {suc u}                 r                  (pred bu)   = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {pred u}                r                  ()
-- lem-a5 {if t₁ then t₂ else t₃} {iszero u}              r                  (iszero bu) = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {if u₁ then u₂ else u₃} r                  (if₁ bu)    = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {if u₁ then u₂ else u₃} r                  (if₂ bu)    = {!!}
-- lem-a5 {if t₁ then t₂ else t₃} {if u₁ then u₂ else u₃} r                  (if₃ bu)    = {!!}
-- -}



-- {-
-- pattern _∷⟨_⟩_ Rxy y R*yz = _∷_ {_} {y} {_} Rxy R*yz

-- lem-2 : ∀ {t u} → wrong ∈* u → W[ o→w t ⟹ u ] → Stuck t
-- lem-2 {t} {.wrong} []                r = lem-1 r
-- lem-2 {t} {u}      (w∈x ∷⟨ x ⟩ x∈*u) r = {!!}
-- -}
-- {-
-- lem-a6 : ∀ {t u} → W[ o→w t ⟹ u ] → BadTerm u → Stuck t
-- lem-a6 {t}                                               {u}                                         r              bu          with O.classify t
-- lem-a6 {t}                                               {u}                                         r              bu          | stu σ                                       = σ
-- lem-a6 {t}                                               {u}                                         r              bu          | val v                                       = r ↯ W.v→nf (ov→wv v)
-- lem-a6 {t}                                               {u}                                         r              bu          | red (u′ , r′)                               with W.⟹-det r (or→wr r′)
-- lem-a6 {t}                                               {.true}                                     r              ()          | red (true , r′)                             | refl
-- lem-a6 {t}                                               {.false}                                    r              ()          | red (false , r′)                            | refl
-- lem-a6 {t}                                               {.zero}                                     r              ()          | red (zero , r′)                             | refl
-- lem-a6 {t}                                               {.(pred (o→w u))}                          r              ()          | red (pred u , r′)                           | refl

-- lem-a6 {.(suc _)}                                        {.(suc (o→w u))}                           (r-suc r)      (suc bu)    | red (suc u , r-suc r′)                      | refl = {!!}
-- lem-a6 {.(suc _)}                                        {.(suc (o→w u))}                           (r-suc r)      (pred bu)   | red (suc u , r-suc r′)                      | refl = {!!}

-- lem-a6 {.(pred (suc (suc u)))}                           {.(suc (o→w u))}                           (r-predSuc nv) (suc bu)    | red (suc u , r-predSuc nv′)                 | refl = {!!}
-- lem-a6 {.(pred (suc (suc u)))}                           {.(suc (o→w u))}                           (r-predSuc nv) (pred bu)   | red (suc u , r-predSuc nv′)                 | refl = {!!}
-- lem-a6 {.(pred (suc (iszero u)))}                        {.(iszero (o→w u))}                        (r-predSuc nv) (iszero bu) | red (iszero u , r-predSuc nv′)              | refl = {!!}
-- lem-a6 {.(pred (suc (if u₁ then u₂ else u₃)))}           {.(if o→w u₁ then o→w u₂ else (o→w u₃))} (r-predSuc nv) (if₁ bu)    | red (if u₁ then u₂ else u₃ , r-predSuc nv′) | refl = {!!}
-- lem-a6 {.(pred (suc (if u₁ then u₂ else u₃)))}           {.(if o→w u₁ then o→w u₂ else (o→w u₃))} (r-predSuc nv) (if₂ bu)    | red (if u₁ then u₂ else u₃ , r-predSuc nv′) | refl = {!!}
-- lem-a6 {.(pred (suc (if u₁ then u₂ else u₃)))}           {.(if o→w u₁ then o→w u₂ else (o→w u₃))} (r-predSuc nv) (if₃ bu)    | red (if u₁ then u₂ else u₃ , r-predSuc nv′) | refl = {!!}

-- lem-a6 {.(iszero _)}                                     {.(iszero (o→w u))}                        (r-iszero r)   (iszero bu) | red (iszero u , r-iszero r′)                | refl = {!!}

-- lem-a6 {.(if true then suc u else _)}                    {.(suc (o→w u))}                           r-ifTrue       (suc bu)    | red (suc u , r-ifTrue)                      | refl = {!!}
-- lem-a6 {.(if true then suc u else _)}                    {.(suc (o→w u))}                           r-ifTrue       (pred bu)   | red (suc u , r-ifTrue)                      | refl = {!!}
-- lem-a6 {.(if true then iszero u else _)}                 {.(iszero (o→w u))}                        r-ifTrue       (iszero bu) | red (iszero u , r-ifTrue)                   | refl = {!!}

-- lem-a6 {.(if false then _ else (suc u))}                 {.(suc (o→w u))}                           r-ifFalse      (suc bu)    | red (suc u , r-ifFalse)                     | refl = {!!}
-- lem-a6 {.(if false then _ else (suc u))}                 {.(suc (o→w u))}                           r-ifFalse      (pred bu)   | red (suc u , r-ifFalse)                     | refl = {!!}
-- lem-a6 {.(if false then _ else (iszero u))}              {.(iszero (o→w u))}                        r-ifFalse      (iszero bu) | red (iszero u , r-ifFalse)                  | refl = {!!}

-- lem-a6 {.(if true then if u₁ then u₂ else u₃ else _)}    {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₁ bu)    | red (if u₁ then u₂ else u₃ , r-ifTrue)      | refl = {!!}
-- lem-a6 {.(if false then _ else (if u₁ then u₂ else u₃))} {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₁ bu)    | red (if u₁ then u₂ else u₃ , r-ifFalse)     | refl = {!!}
-- lem-a6 {.(if _ then u₂ else u₃)}                         {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₁ bu)    | red (if u₁ then u₂ else u₃ , r-if r′)       | refl = {!!}

-- lem-a6 {.(if true then if u₁ then u₂ else u₃ else _)}    {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₂ bu)    | red (if u₁ then u₂ else u₃ , r-ifTrue)      | refl = {!!}
-- lem-a6 {.(if false then _ else (if u₁ then u₂ else u₃))} {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₂ bu)    | red (if u₁ then u₂ else u₃ , r-ifFalse)     | refl = {!!}
-- lem-a6 {.(if _ then u₂ else u₃)}                         {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₂ bu)    | red (if u₁ then u₂ else u₃ , r-if r′)       | refl = {!!}

-- lem-a6 {.(if true then if u₁ then u₂ else u₃ else _)}    {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₃ bu)    | red (if u₁ then u₂ else u₃ , r-ifTrue)      | refl = {!!}
-- lem-a6 {.(if false then _ else (if u₁ then u₂ else u₃))} {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₃ bu)    | red (if u₁ then u₂ else u₃ , r-ifFalse)     | refl = {!!}
-- lem-a6 {.(if _ then u₂ else u₃)}                         {.(if o→w u₁ then o→w u₂ else (o→w u₃))} r              (if₃ bu)    | red (if u₁ then u₂ else u₃ , r-if r′)       | refl = {!!}
-- -}


-- -- lem-a6 {suc t}                      {u}                                 r                  bu          | red (.(suc _)              , r-suc q)        = {!!}
-- -- lem-a6 {.(pred zero)}               {.wrong}                            (r-predWrong ())   wrong       | red (.zero                 , r-predZero)
-- -- lem-a6 {.(pred zero)}               {.zero}                             r-predZero         ()          | red (.zero                 , r-predZero)
-- -- lem-a6 {.(pred zero)}               {.(pred _)}                         (r-pred r)         ()          | red (.zero                 , r-predZero)
-- -- lem-a6 {.(pred (suc t))}            {.wrong}                            (r-predWrong ())   wrong       | red (t                     , r-predSuc nv)
-- -- lem-a6 {.(pred (suc t))}            {.(o→w t)}                         (r-predSuc nv₁)    bu          | red (t                     , r-predSuc nv)   = {!!}
-- -- lem-a6 {.(pred (suc t))}            {.(pred _)}                         (r-pred r)         ()          | red (t                     , r-predSuc nv)
-- -- lem-a6 {.(pred _)}                  {u}                                 r                  bu          | red (.(pred _)             , r-pred q)       = {!!}
-- -- lem-a6 {.(iszero zero)}             {.wrong}                            (r-iszeroWrong ()) wrong       | red (.true                 , r-iszeroZero)
-- -- lem-a6 {.(iszero zero)}             {.true}                             r-iszeroZero       ()          | red (.true                 , r-iszeroZero)
-- -- lem-a6 {.(iszero zero)}             {.(iszero _)}                       (r-iszero r)       (iszero bu) | red (.true                 , r-iszeroZero)   = {!!}
-- -- lem-a6 {.(iszero (suc _))}          {.wrong}                            (r-iszeroWrong ()) wrong       | red (.false                , r-iszeroSuc nv)
-- -- lem-a6 {.(iszero (suc _))}          {.false}                            (r-iszeroSuc nv₁)  ()          | red (.false                , r-iszeroSuc nv)
-- -- lem-a6 {.(iszero (suc _))}          {.(iszero _)}                       (r-iszero r)       (iszero bu) | red (.false                , r-iszeroSuc nv) = {!!}
-- -- lem-a6 {.(iszero _)}                {u}                                 r                  bu          | red (.(iszero _)           , r-iszero q)     = {!!}
-- -- lem-a6 {.(if true then t else _)}   {.wrong}                            (r-ifWrong bb)     bu          | red (t                     , r-ifTrue)       = {!!}
-- -- lem-a6 {.(if true then t else _)}   {.(o→w t)}                         r-ifTrue           bu          | red (t                     , r-ifTrue)       = {!!}
-- -- lem-a6 {.(if true then t else _)}   {.(if _ then o→w t else (o→w _))} (r-if r)           bu          | red (t                     , r-ifTrue)       = {!!}
-- -- lem-a6 {.(if false then _ else t)}  {.wrong}                            (r-ifWrong bb)     bu          | red (t                     , r-ifFalse)      = {!!}
-- -- lem-a6 {.(if false then _ else t)}  {.(o→w t)}                         r-ifFalse          bu          | red (t                     , r-ifFalse)      = {!!}
-- -- lem-a6 {.(if false then _ else t)}  {.(if _ then o→w _ else (o→w t))} (r-if r)           bu          | red (t                     , r-ifFalse)      = {!!}
-- -- lem-a6 {.(if _ then _ else _)}      {u}                                 r                  bu          | red (.(if _ then _ else _) , r-if q)         = {!!}





-- -- postulate
-- --   lem-a5 : ∀ {t u} → W[ o→w t ⟹ u ] → ¬ W.GoodTerm u → Stuck t

-- -- pattern _∷⟨_⟩_ Rxy y Ryz = _∷_ {_} {y} {_} Rxy Ryz

-- -- hm : ∀ t → suc (o→w t) ≡ o→w (suc t)
-- -- hm t = refl

-- -- hmm : ∀ t u → W[ suc (o→w t) ⟹ u ] ≡ W[ o→w (suc t) ⟹ u ]
-- -- hmm t u = refl

-- -- ugh : ∀ {t u} → (gu : W.GoodTerm u) → W[ o→w t ⟹ u ] → O[ t ⟹ w→o gu ]
-- -- ugh {t} {u} gu r with o→w t | w→o gu
-- -- ugh {t} {.wrong}                ()       (r-sucWrong _)     | .(suc _)                  | _
-- -- ugh {t} {suc u}                 (suc gu) (r-suc r)          | (suc t′)                  | x = {!!}
-- -- ugh {t} {.wrong}                ()       (r-predWrong _)    | .(pred _)                 | _
-- -- ugh {t} {.zero}                 gu       r-predZero         | .(pred zero)              | x = {!!}
-- -- ugh {t} {u}                     gu       (r-predSuc nv)     | .(pred (suc u))           | x = {!!}
-- -- ugh {t} {.(pred _)}             gu       (r-pred r)         | .(pred _)                 | x = {!!}
-- -- ugh {t} {.wrong}                ()       (r-iszeroWrong _)  | .(iszero _)               | _
-- -- ugh {t} {.true}                 gu       r-iszeroZero       | .(iszero zero)            | x = {!!}
-- -- ugh {t} {.false}                gu       (r-iszeroSuc nv)   | .(iszero (suc _))         | x = {!!}
-- -- ugh {t} {.(iszero _)}           gu       (r-iszero r)       | .(iszero _)               | x = {!!}
-- -- ugh {t} {.wrong}                ()       (r-ifWrong _)      | .(if _ then _ else _)     | _
-- -- ugh {t} {u}                     gu       r-ifTrue           | .(if true then u else _)  | x = {!!}
-- -- ugh {t} {u}                     gu       r-ifFalse          | .(if false then _ else u) | x = {!!}
-- -- ugh {t} {.(if _ then _ else _)} gu       (r-if r)           | .(if _ then _ else _)     | x = {!!}

-- -- prop-a22 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × O[ t ⟹* u ])
-- -- prop-a22 {true}                  (() ∷ _)
-- -- prop-a22 {false}                 (() ∷ _)
-- -- prop-a22 {zero}                  (() ∷ _)
-- -- prop-a22 {suc t}                 (r  ∷⟨ x ⟩ rs) = {!coerce r (hmm t x)!}
-- -- prop-a22 {pred t}                (r  ∷⟨ x ⟩ rs) = {!!}
-- -- prop-a22 {iszero t}              (r  ∷⟨ x ⟩ rs) = {!!}
-- -- prop-a22 {if t₁ then t₂ else t₃} (r  ∷⟨ x ⟩ rs) = {!!}



-- -- -- w→o : ∀ t → ¬ Wrong t → O.Term
-- -- -- w→o wrong                    ¬w = [] ↯ ¬w
-- -- -- w→o true                     ¬w = true
-- -- -- w→o false                    ¬w = false
-- -- -- w→o zero                     ¬w = zero
-- -- -- w→o (suc wrong)              ¬w = (suc ∷ []) ↯ ¬w
-- -- -- w→o (suc t)                  ¬w = suc (w→o t (undo suc ¬w))
-- -- -- w→o (pred wrong)             ¬w = (pred ∷ []) ↯ ¬w
-- -- -- w→o (pred t)                 ¬w = pred (w→o t (undo pred ¬w))
-- -- -- w→o (iszero wrong)           ¬w = (iszero ∷ []) ↯ ¬w
-- -- -- w→o (iszero t)               ¬w = iszero (w→o t (undo iszero ¬w))
-- -- -- w→o (if wrong then _ else _) ¬w = (if₁ ∷ []) ↯ ¬w
-- -- -- w→o (if _ then wrong else _) ¬w = (if₂ ∷ []) ↯ ¬w
-- -- -- w→o (if _ then _ else wrong) ¬w = (if₃ ∷ []) ↯ ¬w
-- -- -- w→o (if t₁ then t₂ else t₃)  ¬w = if (w→o t₁ (undo if₁ ¬w))
-- -- --                                    then (w→o t₂ (undo if₂ ¬w))
-- -- --                                    else (w→o t₃ (undo if₃ ¬w))

-- -- -- -- wnv→onv : ∀ {t} → (¬w : ¬ Wrong t) → W.NumericValue t → O.NumericValue (w→o t ¬w)
-- -- -- -- wnv→onv ¬w zero     = zero
-- -- -- -- wnv→onv ¬w (suc nv) = {!O.NumericValue.suc (wnv→onv (undo suc ¬w) nv)!}

-- -- -- --   wr→or : ∀ {t₁ t₂} → W[ o→w t₁ ⟹ o→w t₂ ] → O[ t₁ ⟹ t₂ ]
-- -- -- --   wr→or {t₁} {t₂} r = {!!}

-- -- -- --   -- TODO: Can’t figure this out...
-- -- -- --   -- wr→or : ∀ {t₁ t₂} → (¬w₁ : ¬ Wrong t₁) (¬w₂ : ¬ Wrong t₂) →
-- -- -- --   --          W[ t₁ ⟹ t₂ ] → O[ w→o t₁ ¬w₁ ⟹ w→o t₂ ¬w₂ ]
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-sucWrong bn)    = [] ↯ ¬w₂
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-suc r)          = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-predWrong bn)   = [] ↯ ¬w₂
-- -- -- --   -- wr→or ¬w₁ ¬w₂ r-predZero         = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-predSuc nv)     = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-pred r)         = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-iszeroWrong bn) = [] ↯ ¬w₂
-- -- -- --   -- wr→or ¬w₁ ¬w₂ r-iszeroZero       = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-iszeroSuc nv)   = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-iszero r)       = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-ifWrong bb)     = [] ↯ ¬w₂
-- -- -- --   -- wr→or ¬w₁ ¬w₂ r-ifTrue           = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ r-ifFalse          = {!!}
-- -- -- --   -- wr→or ¬w₁ ¬w₂ (r-if r)           = {!!}


-- -- -- -- --   data _↦_ : O.Term → W.Term → Set where
-- -- -- -- --     true                        : true ↦ true
-- -- -- -- --     false                       : false ↦ false
-- -- -- -- --     zero                        : zero ↦ zero
-- -- -- -- --     suc[_/_]                    : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → suc ᵒt ↦ suc ʷt
-- -- -- -- --     pred[_/_]                   : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → pred ᵒt ↦ pred ʷt
-- -- -- -- --     iszero[_/_]                 : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → iszero ᵒt ↦ iszero ʷt
-- -- -- -- --     if[_/_]_then[_/_]_else[_/_] : ∀ ᵒt₁ ʷt₁ → (m₁ : ᵒt₁ ↦ ʷt₁) →
-- -- -- -- --                                   ∀ ᵒt₂ ʷt₂ → (m₂ : ᵒt₂ ↦ ʷt₂) →
-- -- -- -- --                                   ∀ ᵒt₃ ʷt₃ → (m₃ : ᵒt₃ ↦ ʷt₃) →
-- -- -- -- --                                   if ᵒt₁ then ᵒt₂ else ᵒt₃ ↦ if ʷt₁ then ʷt₂ else ʷt₃





-- -- -- -- -- Lemma A.5.

-- -- -- --   -- postulate
-- -- -- --   --   lem-a5 : ∀ {t u} → W[ o→w t ⟹ u ] → Wrong u → Stuck t

-- -- -- --   -- postulate
-- -- -- --   --   lem-a5 : ∀ {ᵒt ʷt u} → ᵒt ↦ ʷt → W[ ʷt ⟹ u ] → Wrong u → Stuck ᵒt

-- -- -- --   -- lem-a5 {true}  () w
-- -- -- --   -- lem-a5 {false} () w
-- -- -- --   -- lem-a5 {zero}  () w
-- -- -- --   -- lem-a5 {suc t} (r-sucWrong bn)    w with o→w t
-- -- -- --   -- lem-a5 {suc t} (r-sucWrong wrong) w | wrong = {!!}
-- -- -- --   -- lem-a5 {suc t} (r-sucWrong true)  w | true  = {!σ-sucTrue!}
-- -- -- --   -- lem-a5 {suc t} (r-sucWrong false) w | false = {!!}
-- -- -- --   -- lem-a5 {suc t} (r-suc r) w = {!!}
-- -- -- --   -- lem-a5 {pred t} r w = {!!}
-- -- -- --   -- lem-a5 {iszero t} r w = {!!}
-- -- -- --   -- lem-a5 {if t₁ then t₂ else t₃} r w = {!!}

-- -- -- -- {-
-- -- -- --   lem-a5 {t} r e with o→w t
-- -- -- --   -- lem-a5 {t} (r-sucWrong bn)    top        | .(suc _)                  = {!!}
-- -- -- --   -- lem-a5 {t} (r-sucWrong bn)    (pop () _) | .(suc _)
-- -- -- --   lem-a5 {t} (r-sucWrong wrong) w          | .(suc wrong)              = {!!}
-- -- -- --   lem-a5 {t} (r-sucWrong true)  w          | .(suc true)               = {!σ-sucTrue!}
-- -- -- --   lem-a5 {t} (r-sucWrong false) w          | .(suc false)              = {!!}
-- -- -- --   lem-a5 {t} (r-suc r)          w          | .(suc _)                  = {!!}
-- -- -- --   -- lem-a5 {t} (r-predWrong bn)   top        | .(pred _)                 = {!!}
-- -- -- --   -- lem-a5 {t} (r-predWrong bn)   (pop () _) | .(pred _)
-- -- -- --   lem-a5 {t} (r-predWrong bn)   w          | .(pred _)                 = {!!}
-- -- -- --   lem-a5 {t} r-predZero         (pop () _) | .(pred zero)
-- -- -- --   lem-a5 {t} (r-predSuc nv)     w          | .(pred (suc _))           = {!!}
-- -- -- --   lem-a5 {t} (r-pred r)         w          | .(pred _)                 = {!!}
-- -- -- --   -- lem-a5 {t} (r-iszeroWrong bn) top        | .(iszero _)               = {!!}
-- -- -- --   -- lem-a5 {t} (r-iszeroWrong bn) (pop () _) | .(iszero _)
-- -- -- --   lem-a5 {t} (r-iszeroWrong bn) w          | .(iszero _)               = {!!}
-- -- -- --   lem-a5 {t} r-iszeroZero       (pop () _) | .(iszero zero)
-- -- -- --   lem-a5 {t} (r-iszeroSuc nv)   (pop () _) | .(iszero (suc _))
-- -- -- --   lem-a5 {t} (r-iszero r)       w          | .(iszero _)               = {!!}
-- -- -- --   -- lem-a5 {t} (r-ifWrong bb)     top        | .(if _ then _ else _)     = {!!}
-- -- -- --   -- lem-a5 {t} (r-ifWrong bb)     (pop () _) | .(if _ then _ else _)
-- -- -- --   lem-a5 {t} (r-ifWrong bb)     w          | .(if _ then _ else _)     = {!!}
-- -- -- --   lem-a5 {t} r-ifTrue           w          | .(if true then _ else _)  = {!!}
-- -- -- --   lem-a5 {t} r-ifFalse          w          | .(if false then _ else _) = {!!}
-- -- -- --   lem-a5 {t} (r-if r)           w          | .(if _ then _ else _)     = {!!}
-- -- -- -- -}

-- -- -- --   -- prop-a22 : ∀ {t u} → Stuck u → W[ o→w t ⟹* wrong ] → O[ t ⟹* u ]
-- -- -- --   -- prop-a22 {t} σ@(¬v , nf) rs with o→w t
-- -- -- --   -- ... | x = {!!}


-- -- -- --   -- postulate
-- -- -- --   --   lem-a5 : ∀ {ᵒt ʷt} → ᵒt ↦ ʷt → W[ ʷt ⟹ wrong ] → Stuck ᵒt
-- -- -- --   --
-- -- -- --   -- prop-a22 : ∀ {ᵒt ʷt} → ᵒt ↦ ʷt → W[ ʷt ⟹* wrong ] → (∃ λ u → Stuck u × O[ ᵒt ⟹* u ])
-- -- -- --   -- prop-a22 true                                                          (() ∷ _)
-- -- -- --   -- prop-a22 false                                                         (() ∷ _)
-- -- -- --   -- prop-a22 zero                                                          (() ∷ _)
-- -- -- --   -- prop-a22 (suc[ ᵒt / ʷt ] m)                                            (r ∷ rs) = {!prop-a22 ? rs!}
-- -- -- --   -- prop-a22 (pred[ ᵒt / ʷt ] m)                                           (r ∷ rs) = {!!}
-- -- -- --   -- prop-a22 (iszero[ ᵒt / ʷt ] m)                                         (r ∷ rs) = {!!}
-- -- -- --   -- prop-a22 (if[ ᵒt₁ / ʷt₁ ] m then[ ᵒt₂ / ʷt₂ ] m₁ else[ ᵒt₃ / ʷt₃ ] m₂) (r ∷ rs) = {!!}

-- -- -- --   -- prop-a22 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × O[ t ⟹* u ])
-- -- -- --   -- prop-a22 rs = {!!}
