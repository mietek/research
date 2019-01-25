{-# OPTIONS --rewriting #-}

module Chapter3a where

open import Chapter3 public

{-# BUILTIN REWRITE _≡_ #-}

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


----------------------------------------------------------------------------------------------------
--
-- Hard part

-- Idea:
-- find first reduction that goes from `u` to `w` such that `w` contains `wrong`.
-- `w→o u` will be our result
-- as long as we started with a `t` that did not contain `wrong` anywhere,
-- all terms up to and including `u` will not contain `wrong` anywhere,
-- because the only rules that produce `wrong` are `*Wrong` rules;
-- therefore we can translate all reductions up to the one that involves `u`.


GoodRed : ∀ {t u} → Pred₀ W[ t ⟹ u ]
GoodRed {t} {u} r = GoodTerm t × GoodTerm u


-- GoodReds : ∀ {t u} → Pred₀ W[ t ⟹* u ]
-- GoodReds []       = ⊤
-- GoodReds (r ∷ rs) = GoodRed r × GoodReds rs
data GoodReds : ∀ {t u} → Pred₀ W[ t ⟹* u ] where
  []  : ∀ {t} → GoodReds {t} {t} []
  _∷_ : ∀ {s t u} {r : W[ s ⟹ t ]} {rs : W[ t ⟹* u ]} →
        GoodRed r → GoodReds rs → GoodReds (r ∷ rs)


-- NOTE: Maybe GoodReds should only store the right-hand GoodTerms?  gt′ is not needed
wrs→ors : ∀ {t u} → (gt : GoodTerm t) (gu : GoodTerm u) (rs : W[ t ⟹* u ]) → GoodReds rs →
           O[ w→o gt ⟹* w→o gu ]
wrs→ors gt gu []       []                 with gt-uniq gt gu
... | refl                                 = []
wrs→ors gt gu (r ∷ rs) ((gt′ , gy) ∷ grs) = wr→or gt gy r ∷ wrs→ors gy gu rs grs



----------------------------------------------------------------------------------------------------


find-0 : ∀ {t} → GoodTerm t → W[ t ⟹* wrong ] → (∃ λ u → GoodTerm u × Σ W[ t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-0 {t} () []
find-0 {t} gt (r ∷⟨ u ⟩ rs)        with good? u
-- ... | no ¬gu                       = t , gt , ([] , tt) , u , ¬gu , r
... | no ¬gu                       = t , gt , ([] , []) , u , ¬gu , r
... | yes gu                       with find-0 gu rs
-- ... | u′ , gu′ , (rs′ , grs′) , vx = u′ , gu′ , ((r ∷ rs′) , ((gt , gu) , grs′)) , vx
... | u′ , gu′ , (rs′ , grs′) , vx = u′ , gu′ , ((r ∷ rs′) , ((gt , gu) ∷ grs′)) , vx


----------------------------------------------------------------------------------------------------


help-0 : ∀ t → GoodTerm (o→w t)
help-0 true                    = true
help-0 false                   = false
help-0 zero                    = zero
help-0 (suc t)                 = suc (help-0 t)
help-0 (pred t)                = pred (help-0 t)
help-0 (iszero t)              = iszero (help-0 t)
help-0 (if t₁ then t₂ else t₃) = if (help-0 t₁) then (help-0 t₂) else (help-0 t₃)


find-1 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → GoodTerm u × Σ W[ o→w t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-1 {t} rs = find-0 (help-0 t) rs


----------------------------------------------------------------------------------------------------


help-1 : ∀ {t} → (gt : GoodTerm t) → o→w (w→o gt) ≡ t
help-1 true                       = refl
help-1 false                      = refl
help-1 zero                       = refl
help-1 (suc gt)                   = suc & help-1 gt
help-1 (pred gt)                  = pred & help-1 gt
help-1 (iszero gt)                = iszero & help-1 gt
help-1 (if gt₁ then gt₂ else gt₃) = if_then_else & help-1 gt₁ ⊗ help-1 gt₂ ⊗ help-1 gt₃


{-# REWRITE help-1 #-}


help-1a : ∀ {t u} → (gt : GoodTerm t) → W[ t ⟹ u ] ≡ W[ o→w (w→o gt) ⟹ u ]
-- help-1a gt = (λ t′ → W[ t′ ⟹ _ ]) & help-1 gt
help-1a gt = refl


help-1b : ∀ {t u} → (gu : GoodTerm u) → W[ t ⟹* u ] ≡ W[ t ⟹* o→w (w→o gu) ]
-- help-1b gu = (λ u′ → W[ _ ⟹* u′ ]) & help-1 gu
help-1b gu = refl


help-1c : ∀ {t u} {rs : W[ o→w t ⟹* u ]} → (gu : GoodTerm u) → GoodReds rs ≡ GoodReds (coerce rs (help-1b gu))
-- help-1c gu = ?
help-1c gu = refl


find-2 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → Σ W[ o→w t ⟹* o→w u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ o→w u ⟹ v ])
find-2 {t} rs with find-1 {t} rs
... | u , gu , (rs′ , grs′) , v , ¬gv , r = w→o gu
                                          , (coerce rs′ (help-1b gu) , coerce grs′ (help-1c {t} gu))
--                                          , (rs′ , grs′)
                                          , v
                                          , ¬gv
                                          , (coerce r (help-1a gu))
--                                          , r


----------------------------------------------------------------------------------------------------


help-2a : ∀ t → GoodTerm (o→w t)
help-2a true                    = true
help-2a false                   = false
help-2a zero                    = zero
help-2a (suc t)                 = suc (help-2a t)
help-2a (pred t)                = pred (help-2a t)
help-2a (iszero t)              = iszero (help-2a t)
help-2a (if t₁ then t₂ else t₃) = if help-2a t₁ then help-2a t₂ else (help-2a t₃)


-- NOTE: Final formulation of Lemma A.5
help-2b : ∀ {u v} → (¬gv : ¬ GoodTerm v) → W[ o→w u ⟹ v ] → Stuck u
help-2b {u} ¬gv r with O.classify u
help-2b {t} ¬gv r | stu σ        = σ
help-2b {t} ¬gv r | val v        = r ↯ W.v→nf (ov→wv v)
help-2b {t} ¬gv r | red (_ , r′) with W.⟹-det r (or→wr r′)
help-2b {t} ¬gv r | red (u , r′) | refl = help-2a u ↯ ¬gv


find-3 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Σ W[ o→w t ⟹* o→w u ] GoodReds × Stuck u)
find-3 {t} rs with find-2 {t} rs
... | u , (rs′ , grs′) , v , ¬gv , r = u , (rs′ , grs′) , help-2b ¬gv r


----------------------------------------------------------------------------------------------------


help-3a : ∀ {t} → (gt : GoodTerm (o→w t)) → w→o gt ≡ t
help-3a {true}                  true                       = refl
help-3a {false}                 false                      = refl
help-3a {zero}                  zero                       = refl
help-3a {suc t}                 (suc gt)                   = suc & help-3a gt
help-3a {pred t}                (pred gt)                  = pred & help-3a gt
help-3a {iszero t}              (iszero gt)                = iszero & help-3a gt
help-3a {if t₁ then t₂ else t₃} (if gt₁ then gt₂ else gt₃) = if_then_else & help-3a gt₁ ⊗ help-3a gt₂ ⊗ help-3a gt₃


help-3b : ∀ {t u} → (gt : GoodTerm (o→w t)) (gu : GoodTerm (o→w u)) → O[ w→o gt ⟹* w→o gu ] → O[ t ⟹* u ]
help-3b {t} {u} gt gu rs rewrite help-3a {t} gt | help-3a {u} gu = rs


help-3c : ∀ {t u} → (rs : W[ o→w t ⟹* o→w u ]) → GoodReds rs → O[ t ⟹* u ]
help-3c {t} {u} rs grs with help-2a t | help-2a u
... | gt | gu = help-3b gt gu (wrs→ors gt gu rs grs)


find-4 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → O[ t ⟹* u ] × Stuck u)
find-4 {t} rs with find-3 {t} rs
... | u , (rs′ , grs′) , σ = u , help-3c rs′ grs′ , σ
