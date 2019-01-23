module Chapter3a where

open import Chapter3 public

open module O = NumbersAndBooleansGetStuck
  renaming (_⟹_ to O[_⟹_] ; _⟹*_ to O[_⟹*_])

open module W = NumbersAndBooleansGoWrong
  renaming (_⟹_ to W[_⟹_] ; _⟹*_ to W[_⟹*_])


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

-- Not needed?
-- ov→wv : ∀ {t} → O.Value t → W.Value (o→w t)
-- ov→wv true     = true
-- ov→wv false    = false
-- ov→wv (num nv) = num (onv→wnv nv)

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


-- Lemma A.4.

lem-a4 : ∀ {t} → Stuck t → W[ o→w t ⟹* wrong ]
lem-a4 {true}                  (¬v , nf) = true ↯ ¬v
lem-a4 {false}                 (¬v , nf) = false ↯ ¬v
lem-a4 {zero}                  (¬v , nf) = num zero ↯ ¬v
lem-a4 {suc t}                 (¬v , nf) with O.classify t
... | stu σ                              = W.map r-suc (lem-a4 σ) W.∷ʳ r-sucWrong wrong
... | val true                           = r-sucWrong true ∷ []
... | val false                          = r-sucWrong false ∷ []
... | val (num nv)                       = num (suc nv) ↯ ¬v
... | red (_ , r)                        = r-suc r ↯ nf
lem-a4 {pred t}                (¬v , nf) with O.classify t
... | stu σ                              = W.map r-pred (lem-a4 σ) W.∷ʳ r-predWrong wrong
... | val true                           = r-predWrong true ∷ []
... | val false                          = r-predWrong false ∷ []
... | val (num zero)                     = r-predZero ↯ nf
... | val (num (suc nv))                 = r-predSuc nv ↯ nf
... | red (_ , r)                        = r-pred r ↯ nf
lem-a4 {iszero t}              (¬v , nf) with O.classify t
... | stu σ                              = W.map r-iszero (lem-a4 σ) W.∷ʳ r-iszeroWrong wrong
... | val true                           = r-iszeroWrong true ∷ []
... | val false                          = r-iszeroWrong false ∷ []
... | val (num zero)                     = r-iszeroZero ↯ nf
... | val (num (suc nv))                 = r-iszeroSuc nv ↯ nf
... | red (_ , r)                        = r-iszero r ↯ nf
lem-a4 {if t₁ then t₂ else t₃} (¬v , nf) with O.classify t₁
... | stu σ₁                             = W.map r-if (lem-a4 σ₁) W.∷ʳ r-ifWrong wrong
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
-- Hard part


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


----------------------------------------------------------------------------------------------------

wr→or : ∀ {t u} → (gt : W.GoodTerm t) (gu : W.GoodTerm u) → W[ t ⟹ u ] →
         O[ w→o gt ⟹ w→o gu ]
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
wr→or (if true then gt₂            else gt₃)
                                    gu                         r-ifTrue          with gt-uniq gt₂ gu
... | refl                                                                       = r-ifTrue
wr→or (if false then gt₂ else gt₃) gu                         r-ifFalse         with gt-uniq gt₃ gu
... | refl                                                                       = r-ifFalse
wr→or (if gt₁ then gt₂ else gt₃)   (if gu₁ then gu₂ else gu₃) (r-if r)          with gt-uniq gt₂ gu₂ | gt-uniq gt₃ gu₃
... | refl | refl                                                                = r-if (wr→or gt₁ gu₁ r)




postulate
  lem-a5 : ∀ {t u} → W[ o→w t ⟹ u ] → ¬ W.GoodTerm u → Stuck t

pattern _∷⟨_⟩_ Rxy y Ryz = _∷_ {_} {y} {_} Rxy Ryz

hm : ∀ t → suc (o→w t) ≡ o→w (suc t)
hm t = refl

hmm : ∀ t u → W[ suc (o→w t) ⟹ u ] ≡ W[ o→w (suc t) ⟹ u ]
hmm t u = refl

ugh : ∀ {t u} → (gu : W.GoodTerm u) → W[ o→w t ⟹ u ] → O[ t ⟹ w→o gu ]
ugh {t} {u} gu r with o→w t | w→o gu
ugh {t} {.wrong}                ()       (r-sucWrong _)     | .(suc _)                  | _
ugh {t} {suc u}                 (suc gu) (r-suc r)          | (suc t′)                  | x = {!!}
ugh {t} {.wrong}                ()       (r-predWrong _)    | .(pred _)                 | _
ugh {t} {.zero}                 gu       r-predZero         | .(pred zero)              | x = {!!}
ugh {t} {u}                     gu       (r-predSuc nv)     | .(pred (suc u))           | x = {!!}
ugh {t} {.(pred _)}             gu       (r-pred r)         | .(pred _)                 | x = {!!}
ugh {t} {.wrong}                ()       (r-iszeroWrong _)  | .(iszero _)               | _
ugh {t} {.true}                 gu       r-iszeroZero       | .(iszero zero)            | x = {!!}
ugh {t} {.false}                gu       (r-iszeroSuc nv)   | .(iszero (suc _))         | x = {!!}
ugh {t} {.(iszero _)}           gu       (r-iszero r)       | .(iszero _)               | x = {!!}
ugh {t} {.wrong}                ()       (r-ifWrong _)      | .(if _ then _ else _)     | _
ugh {t} {u}                     gu       r-ifTrue           | .(if true then u else _)  | x = {!!}
ugh {t} {u}                     gu       r-ifFalse          | .(if false then _ else u) | x = {!!}
ugh {t} {.(if _ then _ else _)} gu       (r-if r)           | .(if _ then _ else _)     | x = {!!}

prop-a22 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × O[ t ⟹* u ])
prop-a22 {true}                  (() ∷ _)
prop-a22 {false}                 (() ∷ _)
prop-a22 {zero}                  (() ∷ _)
prop-a22 {suc t}                 (r  ∷⟨ x ⟩ rs) = {!coerce r (hmm t x)!}
prop-a22 {pred t}                (r  ∷⟨ x ⟩ rs) = {!!}
prop-a22 {iszero t}              (r  ∷⟨ x ⟩ rs) = {!!}
prop-a22 {if t₁ then t₂ else t₃} (r  ∷⟨ x ⟩ rs) = {!!}



-- w→o : ∀ t → ¬ Wrong t → O.Term
-- w→o wrong                    ¬w = [] ↯ ¬w
-- w→o true                     ¬w = true
-- w→o false                    ¬w = false
-- w→o zero                     ¬w = zero
-- w→o (suc wrong)              ¬w = (suc ∷ []) ↯ ¬w
-- w→o (suc t)                  ¬w = suc (w→o t (undo suc ¬w))
-- w→o (pred wrong)             ¬w = (pred ∷ []) ↯ ¬w
-- w→o (pred t)                 ¬w = pred (w→o t (undo pred ¬w))
-- w→o (iszero wrong)           ¬w = (iszero ∷ []) ↯ ¬w
-- w→o (iszero t)               ¬w = iszero (w→o t (undo iszero ¬w))
-- w→o (if wrong then _ else _) ¬w = (if₁ ∷ []) ↯ ¬w
-- w→o (if _ then wrong else _) ¬w = (if₂ ∷ []) ↯ ¬w
-- w→o (if _ then _ else wrong) ¬w = (if₃ ∷ []) ↯ ¬w
-- w→o (if t₁ then t₂ else t₃)  ¬w = if (w→o t₁ (undo if₁ ¬w))
--                                    then (w→o t₂ (undo if₂ ¬w))
--                                    else (w→o t₃ (undo if₃ ¬w))

-- -- wnv→onv : ∀ {t} → (¬w : ¬ Wrong t) → W.NumericValue t → O.NumericValue (w→o t ¬w)
-- -- wnv→onv ¬w zero     = zero
-- -- wnv→onv ¬w (suc nv) = {!O.NumericValue.suc (wnv→onv (undo suc ¬w) nv)!}

-- --   wr→or : ∀ {t₁ t₂} → W[ o→w t₁ ⟹ o→w t₂ ] → O[ t₁ ⟹ t₂ ]
-- --   wr→or {t₁} {t₂} r = {!!}

-- --   -- TODO: Can’t figure this out...
-- --   -- wr→or : ∀ {t₁ t₂} → (¬w₁ : ¬ Wrong t₁) (¬w₂ : ¬ Wrong t₂) →
-- --   --          W[ t₁ ⟹ t₂ ] → O[ w→o t₁ ¬w₁ ⟹ w→o t₂ ¬w₂ ]
-- --   -- wr→or ¬w₁ ¬w₂ (r-sucWrong bn)    = [] ↯ ¬w₂
-- --   -- wr→or ¬w₁ ¬w₂ (r-suc r)          = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-predWrong bn)   = [] ↯ ¬w₂
-- --   -- wr→or ¬w₁ ¬w₂ r-predZero         = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-predSuc nv)     = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-pred r)         = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-iszeroWrong bn) = [] ↯ ¬w₂
-- --   -- wr→or ¬w₁ ¬w₂ r-iszeroZero       = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-iszeroSuc nv)   = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-iszero r)       = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-ifWrong bb)     = [] ↯ ¬w₂
-- --   -- wr→or ¬w₁ ¬w₂ r-ifTrue           = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ r-ifFalse          = {!!}
-- --   -- wr→or ¬w₁ ¬w₂ (r-if r)           = {!!}


-- -- --   data _↦_ : O.Term → W.Term → Set where
-- -- --     true                        : true ↦ true
-- -- --     false                       : false ↦ false
-- -- --     zero                        : zero ↦ zero
-- -- --     suc[_/_]                    : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → suc ᵒt ↦ suc ʷt
-- -- --     pred[_/_]                   : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → pred ᵒt ↦ pred ʷt
-- -- --     iszero[_/_]                 : ∀ ᵒt ʷt → (m : ᵒt ↦ ʷt) → iszero ᵒt ↦ iszero ʷt
-- -- --     if[_/_]_then[_/_]_else[_/_] : ∀ ᵒt₁ ʷt₁ → (m₁ : ᵒt₁ ↦ ʷt₁) →
-- -- --                                   ∀ ᵒt₂ ʷt₂ → (m₂ : ᵒt₂ ↦ ʷt₂) →
-- -- --                                   ∀ ᵒt₃ ʷt₃ → (m₃ : ᵒt₃ ↦ ʷt₃) →
-- -- --                                   if ᵒt₁ then ᵒt₂ else ᵒt₃ ↦ if ʷt₁ then ʷt₂ else ʷt₃





-- -- -- Lemma A.5.

-- --   -- postulate
-- --   --   lem-a5 : ∀ {t u} → W[ o→w t ⟹ u ] → Wrong u → Stuck t

-- --   -- postulate
-- --   --   lem-a5 : ∀ {ᵒt ʷt u} → ᵒt ↦ ʷt → W[ ʷt ⟹ u ] → Wrong u → Stuck ᵒt

-- --   -- lem-a5 {true}  () w
-- --   -- lem-a5 {false} () w
-- --   -- lem-a5 {zero}  () w
-- --   -- lem-a5 {suc t} (r-sucWrong bn)    w with o→w t
-- --   -- lem-a5 {suc t} (r-sucWrong wrong) w | wrong = {!!}
-- --   -- lem-a5 {suc t} (r-sucWrong true)  w | true  = {!σ-sucTrue!}
-- --   -- lem-a5 {suc t} (r-sucWrong false) w | false = {!!}
-- --   -- lem-a5 {suc t} (r-suc r) w = {!!}
-- --   -- lem-a5 {pred t} r w = {!!}
-- --   -- lem-a5 {iszero t} r w = {!!}
-- --   -- lem-a5 {if t₁ then t₂ else t₃} r w = {!!}

-- -- {-
-- --   lem-a5 {t} r e with o→w t
-- --   -- lem-a5 {t} (r-sucWrong bn)    top        | .(suc _)                  = {!!}
-- --   -- lem-a5 {t} (r-sucWrong bn)    (pop () _) | .(suc _)
-- --   lem-a5 {t} (r-sucWrong wrong) w          | .(suc wrong)              = {!!}
-- --   lem-a5 {t} (r-sucWrong true)  w          | .(suc true)               = {!σ-sucTrue!}
-- --   lem-a5 {t} (r-sucWrong false) w          | .(suc false)              = {!!}
-- --   lem-a5 {t} (r-suc r)          w          | .(suc _)                  = {!!}
-- --   -- lem-a5 {t} (r-predWrong bn)   top        | .(pred _)                 = {!!}
-- --   -- lem-a5 {t} (r-predWrong bn)   (pop () _) | .(pred _)
-- --   lem-a5 {t} (r-predWrong bn)   w          | .(pred _)                 = {!!}
-- --   lem-a5 {t} r-predZero         (pop () _) | .(pred zero)
-- --   lem-a5 {t} (r-predSuc nv)     w          | .(pred (suc _))           = {!!}
-- --   lem-a5 {t} (r-pred r)         w          | .(pred _)                 = {!!}
-- --   -- lem-a5 {t} (r-iszeroWrong bn) top        | .(iszero _)               = {!!}
-- --   -- lem-a5 {t} (r-iszeroWrong bn) (pop () _) | .(iszero _)
-- --   lem-a5 {t} (r-iszeroWrong bn) w          | .(iszero _)               = {!!}
-- --   lem-a5 {t} r-iszeroZero       (pop () _) | .(iszero zero)
-- --   lem-a5 {t} (r-iszeroSuc nv)   (pop () _) | .(iszero (suc _))
-- --   lem-a5 {t} (r-iszero r)       w          | .(iszero _)               = {!!}
-- --   -- lem-a5 {t} (r-ifWrong bb)     top        | .(if _ then _ else _)     = {!!}
-- --   -- lem-a5 {t} (r-ifWrong bb)     (pop () _) | .(if _ then _ else _)
-- --   lem-a5 {t} (r-ifWrong bb)     w          | .(if _ then _ else _)     = {!!}
-- --   lem-a5 {t} r-ifTrue           w          | .(if true then _ else _)  = {!!}
-- --   lem-a5 {t} r-ifFalse          w          | .(if false then _ else _) = {!!}
-- --   lem-a5 {t} (r-if r)           w          | .(if _ then _ else _)     = {!!}
-- -- -}

-- --   -- prop-a22 : ∀ {t u} → Stuck u → W[ o→w t ⟹* wrong ] → O[ t ⟹* u ]
-- --   -- prop-a22 {t} σ@(¬v , nf) rs with o→w t
-- --   -- ... | x = {!!}


-- --   -- postulate
-- --   --   lem-a5 : ∀ {ᵒt ʷt} → ᵒt ↦ ʷt → W[ ʷt ⟹ wrong ] → Stuck ᵒt
-- --   --
-- --   -- prop-a22 : ∀ {ᵒt ʷt} → ᵒt ↦ ʷt → W[ ʷt ⟹* wrong ] → (∃ λ u → Stuck u × O[ ᵒt ⟹* u ])
-- --   -- prop-a22 true                                                          (() ∷ _)
-- --   -- prop-a22 false                                                         (() ∷ _)
-- --   -- prop-a22 zero                                                          (() ∷ _)
-- --   -- prop-a22 (suc[ ᵒt / ʷt ] m)                                            (r ∷ rs) = {!prop-a22 ? rs!}
-- --   -- prop-a22 (pred[ ᵒt / ʷt ] m)                                           (r ∷ rs) = {!!}
-- --   -- prop-a22 (iszero[ ᵒt / ʷt ] m)                                         (r ∷ rs) = {!!}
-- --   -- prop-a22 (if[ ᵒt₁ / ʷt₁ ] m then[ ᵒt₂ / ʷt₂ ] m₁ else[ ᵒt₃ / ʷt₃ ] m₂) (r ∷ rs) = {!!}

-- --   -- prop-a22 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × O[ t ⟹* u ])
-- --   -- prop-a22 rs = {!!}
