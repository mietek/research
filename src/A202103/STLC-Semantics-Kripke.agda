module A202103.STLC-Semantics-Kripke where

open import A202103.STLC-Syntax-Convertibility public
open import A202103.STLC-Syntax-Bidirectional public

------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World : Set
    _≥_   : World → World → Set
    idm   : ∀ {W} → W ≥ W
    movm  : ∀ {W W′ W″} → W″ ≥ W′ → W′ ≥ W → W″ ≥ W
    Base  : World → Set
    movb  : ∀ {W W′} → W′ ≥ W → Base W → Base W′

  _/_≥_  = _≥_

open Model

{-# DISPLAY Model._≥_ ℳ W′ W = ℳ / W′ ≥ W #-}

infix 3 _/_⊩_
_/_⊩_ : ∀ ℳ → ℳ .World → Type → Set
ℳ / W ⊩ ◦     = ℳ .Base W
ℳ / W ⊩ A ⊃ B = ∀ {W′} → ℳ / W′ ≥ W → ℳ / W′ ⊩ A → ℳ / W′ ⊩ B

------------------------------------------------------------------------------

-- Higher-order representation of a semantic substitution.
infix 3 _/_⊩*_
_/_⊩*_ : ∀ ℳ → ℳ .World → List Type → Set
ℳ / W ⊩* Ξ = ∀ {A} → Ξ ∋ A → ℳ / W ⊩ A

-- To obtain the result of semantically substituting the topmost index.
headz : ∀ {ℳ W Ξ A} → ℳ / W ⊩* Ξ , A → ℳ / W ⊩ A
headz ζ = ζ top

-- To shorten a semantic substitution.
tailz : ∀ {ℳ W Ξ A} → ℳ / W ⊩* Ξ , A → ℳ / W ⊩* Ξ
tailz ζ = ζ ∘ pop

-- To construct an empty semantic substitution.
nilz : ∀ {ℳ W} → ℳ / W ⊩* ·
nilz ()

-- To extend a semantic substitution.
consz : ∀ {ℳ W Ξ A} → ℳ / W ⊩* Ξ → ℳ / W ⊩ A → ℳ / W ⊩* Ξ , A
consz ζ t top     = t
consz ζ t (pop x) = ζ x

------------------------------------------------------------------------------

-- To move a semantic object (to an accessible world), or monotonicity of `_⊩_` wrt. accessibility.
mov : ∀ {ℳ W W′ A} → ℳ / W′ ≥ W → ℳ / W ⊩ A → ℳ / W′ ⊩ A
mov {ℳ} {A = ◦}     η = λ d → ℳ .movb η d
mov {ℳ} {A = A ⊃ B} η = λ d₁ η′ d₂ → d₁ (ℳ .movm η′ η) d₂

-- To move a semantic substitution (to an accessible world), or monotonicity of `_⊩*_` wrt. accessibility.
movz : ∀ {ℳ W W′ Γ} → ℳ / W′ ≥ W → ℳ / W ⊩* Γ → ℳ / W′ ⊩* Γ
movz η ζ (top {A = A}) = mov {A = A} η (ζ top)
movz η ζ (pop x)       = movz η (ζ ∘ pop) x

------------------------------------------------------------------------------

infix 3 _/_/_⊨_
_/_/_⊨_ : ∀ ℳ → ℳ .World → List Type → Type → Set
ℳ / W / Γ ⊨ A = ℳ / W ⊩* Γ → ℳ / W ⊩ A

⟦var⟧ : ∀ {ℳ W Γ A} → Γ ∋ A → ℳ / W / Γ ⊨ A
⟦var⟧ x ζ = ζ x

⟦lam⟧ : ∀ {ℳ W Γ A B} → (∀ {W′} → ℳ / W′ ≥ W → ℳ / W′ / Γ , A ⊨ B) → ℳ / W / Γ ⊨ A ⊃ B
⟦lam⟧ {ℳ} d₁ ζ η d₂ = d₁ η (consz (movz η ζ) d₂)

⟦app⟧ : ∀ {ℳ W Γ A B} → ℳ / W / Γ ⊨ A ⊃ B → ℳ / W / Γ ⊨ A → ℳ / W / Γ ⊨ B
⟦app⟧ {ℳ} d₁ d₂ = λ ζ → d₁ ζ (ℳ .idm) (d₂ ζ)

------------------------------------------------------------------------------

infix 3 _⊨_
_⊨_ : List Type → Type → Set₁
Γ ⊨ A = ∀ {ℳ W} → ℳ / W / Γ ⊨ A

reflect : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
reflect (var x)                 = ⟦var⟧ x
reflect (lam {A = A} {B} t)     = ⟦lam⟧ {A = A} {B} (λ η → reflect t)
reflect (app {A = A} {B} t₁ t₂) = ⟦app⟧ {A = A} {B} (reflect t₁) (reflect t₂)

{-
-- TODO: Define and use semantic equality instead of _≡_
module _ where
  snd-reflect : ∀ {ℳ W Γ A} {t₁ t₂ : Γ ⊢ A} → t₁ ≅ t₂ → reflect t₁ {ℳ = ℳ} {W} ≡ reflect t₂
  snd-reflect refl≅                    = refl
  snd-reflect (trans≅ k₁ k₂)           = snd-reflect k₁ ⋮ snd-reflect k₂
  snd-reflect (sym≅ k)                 = snd-reflect k ⁻¹
  snd-reflect (lam≅ {A = A} {B} k)     = ⟦lam⟧ {A = A} {B} & fu′ (fu (λ η → snd-reflect k))
  snd-reflect (app≅ {A = A} {B} k₁ k₂) = ⟦app⟧ {A = A} {B} & snd-reflect k₁ ⊗ snd-reflect k₂
  snd-reflect (beta≅ t₁ t₂)            = {!!}
  snd-reflect (eta≅ t)                 = {!!}

  cpt-reflect : ∀ {ℳ W Γ A} {t₁ t₂ : Γ ⊢ A} → reflect t₁ {ℳ = ℳ} {W} ≡ reflect t₂ → t₁ ≅ t₂
  cpt-reflect = {!!}
-}

------------------------------------------------------------------------------

-- The canonical model.
𝒞 : Model
𝒞 = record
      { World = List Type
      ; _≥_   = _⊒_
      ; idm   = idr
      ; movm  = renr
      ; Base  = _⊢≪ ◦
      ; movb  = rench
      }

mutual
  reflect-can : ∀ {Γ A} → Γ ⊢≫ A → 𝒞 / Γ ⊩ A
  reflect-can {A = ◦}     t = ch t
  reflect-can {A = A ⊃ B} t = λ η a → reflect-can (app (renth η t) (reify-can a))

  reify-can : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Γ ⊢≪ A
  reify-can {A = ◦}     t = t
  reify-can {A = A ⊃ B} d = lam (reify-can (d (wkr idr) (reflect-can {A = A} (var top))))

------------------------------------------------------------------------------

reflectz-can : ∀ {Γ Ξ} → Γ ⊢≫* Ξ → 𝒞 / Γ ⊩* Ξ
reflectz-can ζ top     = reflect-can (ζ top)
reflectz-can ζ (pop x) = reflectz-can (ζ ∘ pop) x

-- Identity of semantic substitution.
idz : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
idz = reflectz-can idths

reify : ∀ {Γ A} → Γ ⊨ A → Γ ⊢≪ A
reify d = reify-can (d idz)

-- Normalization by evaluation.
nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢≪ A
nbe t = reify (reflect t)

------------------------------------------------------------------------------

-- XXX: Moving towards `complete-nbe`.

-- XXX: Convertibility between terms and semantic objects?
infix 3 _≈_
_≈_ : ∀ {Γ A} → Γ ⊢ A → 𝒞 / Γ ⊩ A → Set
_≈_ {Γ} {A = ◦}     t  t′ = t ≅ embch t′
_≈_ {Γ} {A = A ⊃ B} t₁ d₁ = ∀ {Γ′} (η : Γ′ ⊒ Γ) {t₂ : Γ′ ⊢ A} {d₂ : 𝒞 / Γ′ ⊩ A} (p : t₂ ≈ d₂) →
                            app (ren η t₁) t₂ ≈ d₁ η d₂

-- XXX: `_≈_` lifted to contexts; some sort of substitution?
infix 3 _≈*_
_≈*_ : ∀ {Γ Ξ} → Γ ⊢* Ξ → 𝒞 / Γ ⊩* Ξ → Set
_≈*_ {Ξ = Ξ} σ ζ = ∀ {A} (x : Ξ ∋ A) → σ x ≈ ζ x

head≈* : ∀ {Γ Ξ A} {σ : Γ ⊢* Ξ , A} {ζ : 𝒞 / Γ ⊩* Ξ , A} →
         σ ≈* ζ → heads σ ≈ headz ζ
head≈* ω = ω top

tail≈* : ∀ {Γ Ξ A} {σ : Γ ⊢* Ξ , A} {ζ : 𝒞 / Γ ⊩* Ξ , A} →
         σ ≈* ζ → tails σ ≈* tailz ζ
tail≈* ω = ω ∘ pop

nil≈* : ∀ {Γ} → nils {Γ = Γ} ≈* nilz
nil≈* ()

cons≈* : ∀ {Γ Ξ A} {σ : Γ ⊢* Ξ} {ζ : 𝒞 / Γ ⊩* Ξ} {t : Γ ⊢ A} {d : 𝒞 / Γ ⊩ A} →
         σ ≈* ζ → t ≈ d → conss σ t ≈* consz ζ d
cons≈* ω q top     = q
cons≈* ω q (pop x) = ω x

------------------------------------------------------------------------------

-- XXX: Was `coe≫` with reversed arguments.
cast≈ : ∀ {Γ A} {t t′ : Γ ⊢ A} {d : 𝒞 / Γ ⊩ A} →
        t ≈ d → t ≅ t′ → t′ ≈ d
cast≈ {A = ◦}     q  p = trans (sym p) q
cast≈ {A = A ⊃ B} q₁ p = λ η q₂ → cast≈ (q₁ η q₂) (cong-app (thm₁ η p) refl)

-- XXX: Was `acc≫`; name?
lem₂ : ∀ {Γ Γ′ A} {t : Γ ⊢ A} {d : 𝒞 / Γ ⊩ A} (η : Γ′ ⊒ Γ) →
       t ≈ d → ren η t ≈ mov {ℳ = 𝒞} {A = A} η d
lem₂ {A = ◦}     {t} {t′} η p  = cast (thm₁ η p)
                                      ((ren η t ≅_) & (nat-embch η t′ ⁻¹))
lem₂ {A = A ⊃ B} {t₁}     η q₁ = λ η′ {t₂} q₂ → cast (q₁ (renr η′ η) q₂)
                                                      ( (λ t₁′ → app t₁′ t₂ ≈ _)
                                                      & comp-ren-renr η′ η t₁)

-- XXX: Was `_⬖≫_`; name?
lem₂* : ∀ {Γ Γ′ Ξ} {σ : Γ ⊢* Ξ} {ζ : 𝒞 / Γ ⊩* Ξ} (η : Γ′ ⊒ Γ) →
        σ ≈* ζ → rens η σ ≈* movz {ℳ = 𝒞} η ζ
lem₂* η q top     = lem₂ η (q top)
lem₂* η q (pop x) = lem₂* η (q ∘ pop) x

-- XXX: Was `get≫`; may be unnecessary?
lem₃ : ∀ {Γ Ξ A} {σ : Γ ⊢* Ξ} {ζ : 𝒞 / Γ ⊩* Ξ} (x : Ξ ∋ A) →
       σ ≈* ζ → subi σ x ≈ ⟦var⟧ x ζ
lem₃ x q = q x

lem₄-aux₁ : ∀ {Γ Ξ A C} (σ : Γ ⊢* Ξ) (t : Γ ⊢ C) (x : Ξ , C ∋ A) →
           subs (conss ids t) (lifts σ) x ≡ conss σ t x
lem₄-aux₁ σ t top     = refl
lem₄-aux₁ σ t (pop x) = comp-subs-subr (conss ids t) pop σ x ⁻¹
                      ⋮ lid-subs σ x

-- XXX: Was `eval≫`; name?
lem₄ : ∀ {Γ Ξ A} {σ : Γ ⊢* Ξ} {ζ : 𝒞 / Γ ⊩* Ξ} (t : Ξ ⊢ A) →
       σ ≈* ζ → sub σ t ≈ reflect t ζ
lem₄         (var x)     q = lem₃ x q
lem₄ {σ = σ} (lam t)     q =
  λ η {t′} q′ → cast≈ (lem₄ t (cons≈* (lem₂* η q) q′))
                       (cast (sym (red-app-lam _ _))
                             ( (_≅ app (lam _) _)
                             & ( comp-sub-subr (conss ids t′) (liftr η) (sub (lifts σ) t) ⁻¹
                               ⋮ comp-sub-subs (subr (conss ids t′) (liftr η)) (lifts σ) t ⁻¹
                               ⋮ ( flip sub t
                                 & (fu′ (fu λ x → comp-subs-subr (conss ids t′) (liftr η) (lifts σ) x
                                                 ⋮ ha (ha′ ( subs (conss ids t′)
                                                           & fu′ (fu λ x′ → comp-lifts-rens η σ x′ ⁻¹))) x
                                                 ⋮ lem₄-aux₁ (rens η σ) t′ x))))))
lem₄         (app t₁ t₂) q = cast (lem₄ t₁ q idr (lem₄ t₂ q))
                                  ((λ t₁′ → app t₁′ _ ≈ _) & id-ren _)

mutual
  -- XXX: Was `reflect≫`.
  reflect-can≈ : ∀ {Γ A} (t : Γ ⊢≫ A) → embth t ≈ reflect-can t
  reflect-can≈ {A = ◦}     t  = refl
  reflect-can≈ {A = A ⊃ B} t₁ =
    λ η {t₂} {d₂} q → cast≈ (reflect-can≈ (app (renth η t₁) (reify-can d₂)))
                             (cong-app (≅←≡ (nat-embth η t₁)) (sym (reify-can≈ q)))

  -- XXX: Was `reify≫`.
  reify-can≈ : ∀ {Γ A} {t : Γ ⊢ A} {d : 𝒞 / Γ ⊩ A} →
           t ≈ d → t ≅ embch (reify-can d)
  reify-can≈ {A = ◦}     {t} p = p
  reify-can≈ {A = A ⊃ B} {t} q = trans (exp-lam t)
                                       (cong-lam (reify-can≈ (q (wkr idr) (reflect-can≈ (var top)))))

-- TODO: Naming! Naming everywhere!

embths : ∀ {Γ A} → Γ ⊢≫* A → Γ ⊢* A
embths σ top     = embth (σ top)
embths σ (pop x) = embths (σ ∘ pop) x

nat-embths : ∀ {Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Γ ⊢≫* Ξ) (x : Ξ ∋ A) →
             embths (renths η σ) x ≡ rens η (embths σ) x
nat-embths η σ top     = nat-embth η (σ top)
nat-embths η σ (pop x) = nat-embths η (σ ∘ pop) x

reflectz-can≈ : ∀ {Γ Ξ} (σ : Γ ⊢≫* Ξ) →
                embths σ ≈* reflectz-can σ
reflectz-can≈ σ top     = reflect-can≈ (σ top)
reflectz-can≈ σ (pop x) = reflectz-can≈ (σ ∘ pop) x

lem₅ : ∀ {Γ Ξ A} (σ : Γ ⊢≫* Ξ) (x : Ξ ∋ A) → embths σ x ≡ embth (σ x)
lem₅ σ top     = refl
lem₅ σ (pop x) = lem₅ (σ ∘ pop) x

-- XXX: Was `id≫*`.
id≈* : ∀ {Γ} → ids {Γ} ≈* idz
id≈* x = cast (reflectz-can≈ idths x)
              ((_≈ idz x) & lem₅ idths x)

------------------------------------------------------------------------------

-- TODO: It seems that we obtain sound-nbe by virtue of intrinsically well-typed term representation.
module _ where
  -- sound-nbe : ∀ {Γ A} (t : Γ ⊢ A) → Normal (nbe t)

  complete-nbe : ∀ {Γ A} (t : Γ ⊢ A) → t ≅ embch (nbe t)
  complete-nbe t = cast (reify-can≈ (lem₄ t id≈*))
                        ((_≅ embch (nbe t)) & id-sub t)

{-
module _ where
  sound-dec : ∀ {Γ A} {t₁ t₂ : Γ ⊢ A} → t₁ ≅ t₂ → nbe t₁ ≡ nbe t₂
  sound-dec = {!!}

  complete-dec : ∀ {Γ A} {t₁ t₂ : Γ ⊢ A} → nbe t₁ ≡ nbe t₂ → t₁ ≅ t₂
  complete-dec = {!!}
-}

------------------------------------------------------------------------------



------------------------------------------------------------------------------
