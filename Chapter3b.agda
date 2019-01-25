{-# OPTIONS --rewriting #-}

module Chapter3b where

open import Chapter3a public

{-# BUILTIN REWRITE _≡_ #-}

open O
  renaming (_⟹_ to O[_⟹_] ; _⟹*_ to O[_⟹*_] ; _⟹*′_ to O[_⟹*′_])

open W
  renaming (_⟹_ to W[_⟹_] ; _⟹*_ to W[_⟹*_] ; _⟹*′_ to W[_⟹*′_])


----------------------------------------------------------------------------------------------------
--
-- Hard part


-- wrs→ors : ∀ {t u} → (gt : W.GoodTerm t) (gu : W.GoodTerm u) → W[ t ⟹* u ] → O[ w→o gt ⟹* w→o gu ]
-- wrs→ors gt gu []            with gt-uniq gt gu
-- ... | refl                   = []
-- wrs→ors gt gu (r ∷⟨ x ⟩ rs) with good? x
-- ... | yes gx                 = wr→or gt gx r ∷ wrs→ors gx gu rs
-- ... | no ¬gx                 = {!!}
--
-- wrs→ors′ : ∀ {t u} → (gt : W.GoodTerm t) (gu : W.GoodTerm u) → W[ t ⟹*′ u ] → O[ w→o gt ⟹*′ w→o gu ]
-- wrs→ors′ gt gu []′             with gt-uniq gt gu
-- ... | refl                      = []′
-- wrs→ors′ gt gu (rs ∷ʳ′⟨ x ⟩ r) with good? x
-- ... | yes gx                    = wrs→ors′ gt gx rs ∷ʳ′ wr→or gx gu r
-- ... | no ¬gx                    = {!!}
--
-- wrs→ors″ : ∀ {t u} → (gt : W.GoodTerm t) → W[ t ⟹*′ o→w u ] → O[ w→o gt ⟹*′ u ]
-- wrs→ors″ = {!!}

lem-2 : ∀ {t} → W[ o→w t ⟹ wrong ] → Stuck t
lem-2 {t} r                                 with O.classify t
lem-2 {t} r | stu σ                         = σ
lem-2 {t} r | val v                         = r ↯ W.v→nf (ov→wv v)
lem-2 {t} r | red (_                  , r′) with W.⟹-det r (or→wr r′)
lem-2 {t} r | red (true               , r′) | ()
lem-2 {t} r | red (false              , r′) | ()
lem-2 {t} r | red (zero               , r′) | ()
lem-2 {t} r | red (suc _              , r′) | ()
lem-2 {t} r | red (pred _             , r′) | ()
lem-2 {t} r | red (iszero _           , r′) | ()
lem-2 {t} r | red (if _ then _ else _ , r′) | ()

-- lem-3 : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × O[ t ⟹* u ])
-- lem-3 {true} (_∷_ {.true} {t} {u} r rs) = {!!}
-- lem-3 {false} rs = {!!}
-- lem-3 {zero} rs = {!!}
-- lem-3 {suc t} rs = {!!}
-- lem-3 {pred t} rs = {!!}
-- lem-3 {iszero t} rs = {!!}
-- lem-3 {if t₁ then t₂ else t₃} rs = {!!}
--
-- lem-3′ : ∀ {t} → W[ o→w t ⟹*′ wrong ] → (∃ λ u → Stuck u × O[ t ⟹*′ u ])
-- lem-3′ {true} (rs ∷ʳ′⟨ u ⟩ r) with W.classify u
-- ... | val v = r ↯ W.v→nf v
-- ... | red (_ , r′) with W.⟹-det r r′
-- ... | refl = {!!}
-- lem-3′ {false} rs = {!!}
-- lem-3′ {zero} rs = {!!}
-- lem-3′ {suc t} rs = {!!}
-- lem-3′ {pred t} rs = {!!}
-- lem-3′ {iszero t} rs = {!!}
-- lem-3′ {if t₁ then t₂ else t₃} rs = {!!}




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


find-0 : ∀ {t} → GoodTerm t → W[ t ⟹* wrong ] →
         (∃ λ u → GoodTerm u × Σ W[ t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-0 {t} () []
find-0 {t} gt (r ∷⟨ u ⟩ rs)        with good? u
-- ... | no ¬gu                       = t , gt , ([] , tt) , u , ¬gu , r
... | no ¬gu                       = t , gt , ([] , []) , u , ¬gu , r
... | yes gu                       with find-0 gu rs
-- ... | u′ , gu′ , (rs′ , grs′) , vx = u′ , gu′ , ((r ∷ rs′) , ((gt , gu) , grs′)) , vx
... | u′ , gu′ , (rs′ , grs′) , vx = u′ , gu′ , ((r ∷ rs′) , ((gt , gu) ∷ grs′)) , vx


help-0 : ∀ t → GoodTerm (o→w t)
help-0 true                    = true
help-0 false                   = false
help-0 zero                    = zero
help-0 (suc t)                 = suc (help-0 t)
help-0 (pred t)                = pred (help-0 t)
help-0 (iszero t)              = iszero (help-0 t)
help-0 (if t₁ then t₂ else t₃) = if (help-0 t₁) then (help-0 t₂) else (help-0 t₃)


find-1 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → GoodTerm u × Σ W[ o→w t ⟹* u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ u ⟹ v ])
find-1 {t} rs = find-0 (help-0 t) rs


help-1 : ∀ {t} → (gt : GoodTerm t) →
         o→w (w→o gt) ≡ t
help-1 true                       = refl
help-1 false                      = refl
help-1 zero                       = refl
help-1 (suc gt)                   = suc & help-1 gt
help-1 (pred gt)                  = pred & help-1 gt
help-1 (iszero gt)                = iszero & help-1 gt
help-1 (if gt₁ then gt₂ else gt₃) = if_then_else & help-1 gt₁ ⊗ help-1 gt₂ ⊗ help-1 gt₃


{-# REWRITE help-1 #-}


help-1a : ∀ {t u} → (gt : GoodTerm t) →
          W[ t ⟹ u ] ≡ W[ o→w (w→o gt) ⟹ u ]
-- help-1a gt = (λ t′ → W[ t′ ⟹ _ ]) & help-1 gt
help-1a gt = refl


help-1b : ∀ {t u} → (gu : GoodTerm u) →
          W[ t ⟹* u ] ≡ W[ t ⟹* o→w (w→o gu) ]
-- help-1b gu = (λ u′ → W[ _ ⟹* u′ ]) & help-1 gu
help-1b gu = refl


help-1c : ∀ {t u} {rs : W[ o→w t ⟹* u ]} → (gu : GoodTerm u) →
          GoodReds rs ≡ GoodReds (coerce rs (help-1b gu))
-- help-1c gu = ?
help-1c gu = refl


find-2 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → Σ W[ o→w t ⟹* o→w u ] GoodReds × ∃ λ v → ¬ GoodTerm v × W[ o→w u ⟹ v ])
find-2 {t} rs with find-1 rs
... | u , gu , (rs′ , grs′) , v , ¬gv , r = w→o gu
--                                          , (coerce rs′ (help-1b gu) , coerce grs′ (help-1c gu))
                                          , (rs′ , grs′)
                                          , v
                                          , ¬gv
--                                          , (coerce r (help-1a gu))
                                          , r


help-2a : ∀ t → GoodTerm (o→w t)
help-2a true                    = true
help-2a false                   = false
help-2a zero                    = zero
help-2a (suc t)                 = suc (help-2a t)
help-2a (pred t)                = pred (help-2a t)
help-2a (iszero t)              = iszero (help-2a t)
help-2a (if t₁ then t₂ else t₃) = if help-2a t₁ then help-2a t₂ else (help-2a t₃)


help-2b : ∀ {u v} → (¬gv : ¬ GoodTerm v) → W[ o→w u ⟹ v ] →
         Stuck u
help-2b {u} ¬gv r with O.classify u
help-2b {t} ¬gv r | stu σ        = σ
help-2b {t} ¬gv r | val v        = r ↯ W.v→nf (ov→wv v)
help-2b {t} ¬gv r | red (_ , r′) with W.⟹-det r (or→wr r′)
help-2b {t} ¬gv r | red (u , r′) | refl = help-2a u ↯ ¬gv


find-3 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → Σ W[ o→w t ⟹* o→w u ] GoodReds × Stuck u)
find-3 {t} rs with find-2 rs
... | u , (rs′ , grs′) , v , ¬gv , r = u , (rs′ , grs′) , help-2b ¬gv r


help-3w : ∀ {t} → (gt : GoodTerm (o→w t)) → w→o gt ≡ t
help-3w {true}                  true                       = refl
help-3w {false}                 false                      = refl
help-3w {zero}                  zero                       = refl
help-3w {suc t}                 (suc gt)                   = suc & help-3w gt
help-3w {pred t}                (pred gt)                  = pred & help-3w gt
help-3w {iszero t}              (iszero gt)                = iszero & help-3w gt
help-3w {if t₁ then t₂ else t₃} (if gt₁ then gt₂ else gt₃) = if_then_else & help-3w gt₁ ⊗ help-3w gt₂ ⊗ help-3w gt₃

{-# REWRITE help-3w #-}


help-3a : ∀ {t u} → (gt : GoodTerm (o→w t)) (gu : GoodTerm (o→w u)) → O[ w→o gt ⟹ w→o gu ] →
          O[ t ⟹ u ]
-- uses rewrite rule help-3w
help-3a gt gu r = r


help-3b : ∀ {t u} → W[ o→w t ⟹ o→w u ] →
          O[ t ⟹ u ]
help-3b {t} {u} r with help-2a t | help-2a u
... | gt | gu = help-3a gt gu (wr→or gt gu r)


help-3c : ∀ {t u} → (gt : GoodTerm (o→w t)) (gu : GoodTerm (o→w u)) → O[ w→o gt ⟹* w→o gu ] →
          O[ t ⟹* u ]
-- uses rewrite rule help-3w
help-3c gt gu rs = rs


-- NOTE: Maybe GoodReds should only store the right-hand GoodTerms?  gt′ is not needed
wrs→ors : ∀ {t u} → (gt : GoodTerm t) (gu : GoodTerm u) (rs : W[ t ⟹* u ]) → GoodReds rs →
           O[ w→o gt ⟹* w→o gu ]
wrs→ors gt gu []       []                 with gt-uniq gt gu
... | refl                                 = []
wrs→ors gt gu (r ∷ rs) ((gt′ , gy) ∷ grs) = wr→or gt gy r ∷ wrs→ors gy gu rs grs


help-3d : ∀ {t u} → (rs : W[ o→w t ⟹* o→w u ]) → GoodReds rs →
          O[ t ⟹* u ]
help-3d {t} {u} rs grs with help-2a t | help-2a u
... | gt | gu = help-3c gt gu (wrs→ors gt gu rs grs)


-- NOTE: GoodReds may be redundant! Or not!
help-3z : ∀ {t u} → (rs : W[ o→w t ⟹* o→w u ]) → GoodReds rs →
          O[ t ⟹* u ]
help-3z {t} {u} rs grs = help-3d rs grs


find-4 : ∀ {t} → W[ o→w t ⟹* wrong ] →
         (∃ λ u → O[ t ⟹* u ] × Stuck u)
find-4 {t} rs with find-3 rs
... | u , (rs′ , grs′) , σ = u , help-3z rs′ grs′ , σ


-- {-
-- find′ : ∀ {t} → t ≢ wrong → W[ t ⟹*′ wrong ] → (∃ λ u → W[ u ⟹ wrong ] × W[ t ⟹*′ u ])
-- find′ t≢wrong []′ = refl ↯ t≢wrong
-- find′ t≢wrong (rs ∷ʳ′ r) = _ , r , rs

-- find : ∀ {t} → t ≢ wrong → W[ t ⟹* wrong ] → (∃ λ u → W[ u ⟹ wrong ] × W[ t ⟹* u ])
-- find t≢wrong rs with find′ t≢wrong (*→*′ rs)
-- ... | u , r , rs′ = u , r , *′→* rs′

-- o-find : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → W[ u ⟹ wrong ] × W[ o→w t ⟹* u ])
-- o-find {true}                  rs = find (λ ()) rs
-- o-find {false}                 rs = find (λ ()) rs
-- o-find {zero}                  rs = find (λ ()) rs
-- o-find {suc t}                 rs = find (λ ()) rs
-- o-find {pred t}                rs = find (λ ()) rs
-- o-find {iszero t}              rs = find (λ ()) rs
-- o-find {if t₁ then t₂ else t₃} rs = find (λ ()) rs


-- o-find′ : ∀ {t} → W[ o→w t ⟹* wrong ] → (∃ λ u → Stuck u × W[ o→w t ⟹* o→w u ])
-- o-find′ rs with o-find rs
-- ... | u , r , rs′ with good? u
-- ... | yes gu = w→o gu , lem-2 (coerce r (lem-3a gu)) , coerce rs′ (lem-3b gu)
-- ... | no ¬gu = {!!}
-- -}



-- -- lem-3 {true}  (() ∷ _)
-- -- lem-3 {false} (() ∷ _)
-- -- lem-3 {zero}  (() ∷ _)
-- -- lem-3 {suc t}                 (r ∷ rs) = {!!}
-- -- lem-3 {pred t}                (r ∷ rs) = {!!}
-- -- lem-3 {iszero t}              (r ∷ rs) = {!!}
-- -- lem-3 {if t₁ then t₂ else t₃} (r ∷ rs) = {!!}

-- -- lem-3′ : ∀ {t} → W[ o→w t ⟹*′ wrong ] → (∃ λ u → Stuck u × O[ t ⟹*′ u ])
-- -- lem-3′ {true}                  (rs ∷ʳ′⟨ t ⟩ r) with good? t
-- -- lem-3′ {true}                  (rs ∷ʳ′⟨ t ⟩ r) | no ¬gt with ¬gt→bt′ ¬gt
-- -- lem-3′ {true}                  (rs ∷ʳ′⟨ t ⟩ r) | no ¬gt | bt = {!!}
-- -- lem-3′ {true}                  (rs ∷ʳ′⟨ t ⟩ r) | yes gt with lem-1 gt
-- -- lem-3′ {true}                  (rs ∷ʳ′⟨ t ⟩ r) | yes gt | s , refl = s , lem-2 r , wrs→ors″ true rs
-- -- lem-3′ {false}                 (rs ∷ʳ′ r) = {!!}
-- -- lem-3′ {zero}                  (rs ∷ʳ′ r) = {!!}
-- -- lem-3′ {suc t}                 (rs ∷ʳ′ r) = {!!}
-- -- lem-3′ {pred t}                (rs ∷ʳ′ r) = {!!}
-- -- lem-3′ {iszero t}              (rs ∷ʳ′ r) = {!!}
-- -- lem-3′ {if t₁ then t₂ else t₃} (rs ∷ʳ′ r) = {!!}
