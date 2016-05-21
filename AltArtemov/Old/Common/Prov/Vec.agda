module AltArtemov.Common.Prov.Vec where

open import AltArtemov.Common.True.Basic renaming (ᵗ⌊_⌋ to ᵗ⌊_⌋ᵀ) public


data Prov (Γ : Cx) : ∀ {k n} → Vec ᵍ⌊ Γ ⌋ k n → Ty k → Set where
  var  : ∀ {k n} {A : Ty k} (x : Var Γ A) →
           Prov Γ (VARs {k = k} {n = n} ⁱ⌊ x ⌋) A
  lam  : ∀ {k n} {ts : Vec (suc ᵍ⌊ Γ ⌋) k n} {A B : Ty k} → Prov (Γ , A) ts B →
           Prov Γ (LAMs ts) (A ⊃ B)
  app  : ∀ {k n} {ts₁ ts₂ : Vec ᵍ⌊ Γ ⌋ k n} {A B : Ty k} → Prov Γ ts₁ (A ⊃ B) → Prov Γ ts₂ A →
           Prov Γ (APPs ts₁ ts₂) B
  pair : ∀ {k n} {ts₁ ts₂ : Vec ᵍ⌊ Γ ⌋ k n} {A B : Ty k} → Prov Γ ts₁ A → Prov Γ ts₂ B →
           Prov Γ (PAIRs ts₁ ts₂) (A ∧ B)
  fst  : ∀ {k n} {ts : Vec ᵍ⌊ Γ ⌋ k n} {A B : Ty k} → Prov Γ ts (A ∧ B) →
           Prov Γ (FSTs ts) A
  snd  : ∀ {k n} {ts : Vec ᵍ⌊ Γ ⌋ k n} {A B : Ty k} → Prov Γ ts (A ∧ B) →
           Prov Γ (SNDs ts) B
  up   : ∀ {k n} {ts : Vec ᵍ⌊ Γ ⌋ (suc k) n} {u : Tm 0 k} {A : Ty k} → Prov Γ ts (u ∶ A) →
           Prov Γ (UPs ts) ((! u ∶ u ∶ A))
  down : ∀ {k n} {ts : Vec ᵍ⌊ Γ ⌋ (suc k) n} {u : Tm 0 k} {A : Ty k} → Prov Γ ts (u ∶ A) →
           Prov Γ (DOWNs ts) A

ᵗ⌊_⌋ : ∀ {Γ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k n} → Prov Γ ts A → Tm ᵍ⌊ Γ ⌋ (n + k)
ᵗ⌊ var x ⌋      = VAR ⁱ⌊ x ⌋
ᵗ⌊ lam j ⌋      = LAM ᵗ⌊ j ⌋
ᵗ⌊ app j₁ j₂ ⌋  = APP ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ pair j₁ j₂ ⌋ = PAIR ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ fst j ⌋      = FST ᵗ⌊ j ⌋
ᵗ⌊ snd j ⌋      = SND ᵗ⌊ j ⌋
ᵗ⌊_⌋ {Γ} {n = n} (up {k} j)   = subst (Tm ᵍ⌊ Γ ⌋) (suc-plus (suc k) n) (UP ᵗ⌊ j ⌋)
ᵗ⌊_⌋ {Γ} {n = n} (down {k} j) = DOWN (subst (Tm ᵍ⌊ Γ ⌋) (sym (suc-plus k n)) ᵗ⌊ j ⌋)

true⇒ : ∀ {Γ k} {A : Ty k} → True Γ A → Prov Γ [] A
true⇒ (var x)      = var x
true⇒ (lam j)      = lam (true⇒ j)
true⇒ (app j₁ j₂)  = app (true⇒ j₁) (true⇒ j₂)
true⇒ (pair j₁ j₂) = pair (true⇒ j₁) (true⇒ j₂)
true⇒ (fst j)      = fst (true⇒ j)
true⇒ (snd j)      = snd (true⇒ j)
true⇒ (up j)       = up (true⇒ j)
true⇒ (down j)     = down (true⇒ j)

true⇐ : ∀ {Γ k} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k 0} → Prov Γ ts A → True Γ A
true⇐ (var x)      = var x
true⇐ (lam j)      = lam (true⇐ j)
true⇐ (app j₁ j₂)  = app (true⇐ j₁) (true⇐ j₂)
true⇐ (pair j₁ j₂) = pair (true⇐ j₁) (true⇐ j₂)
true⇐ (fst j)      = fst (true⇐ j)
true⇐ (snd j)      = snd (true⇐ j)
true⇐ (up j)       = up (true⇐ j)
true⇐ (down j)     = down (true⇐ j)

true⇒⇐-id : ∀ {Γ k} {A : Ty k} (j : True Γ A) → true⇐ (true⇒ j) ≡ j
true⇒⇐-id (var x)      = refl
true⇒⇐-id (lam j)      = cong lam (true⇒⇐-id j)
true⇒⇐-id (app j₁ j₂)  = cong₂ app (true⇒⇐-id j₁) (true⇒⇐-id j₂)
true⇒⇐-id (pair j₁ j₂) = cong₂ pair (true⇒⇐-id j₁) (true⇒⇐-id j₂)
true⇒⇐-id (fst j)      = cong fst (true⇒⇐-id j)
true⇒⇐-id (snd j)      = cong snd (true⇒⇐-id j)
true⇒⇐-id (up j)       = cong up (true⇒⇐-id j)
true⇒⇐-id (down j)     = cong down (true⇒⇐-id j)

true⇗ : ∀ {Γ k} {A : Ty k} (j : True Γ A) → Prov Γ [ ᵗ⌊ j ⌋ᵀ ] A
true⇗ (var x)      = var x
true⇗ (lam j)      = lam (true⇗ j)
true⇗ (app j₁ j₂)  = app (true⇗ j₁) (true⇗ j₂)
true⇗ (pair j₁ j₂) = pair (true⇗ j₁) (true⇗ j₂)
true⇗ (fst j)      = fst (true⇗ j)
true⇗ (snd j)      = snd (true⇗ j)
true⇗ (up j)       = up (true⇗ j)
true⇗ (down j)     = down (true⇗ j)

true⇙ : ∀ {Γ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k n} → Prov Γ ts A → True Γ A
true⇙ (var x)      = var x
true⇙ (lam j)      = lam (true⇙ j)
true⇙ (app j₁ j₂)  = app (true⇙ j₁) (true⇙ j₂)
true⇙ (pair j₁ j₂) = pair (true⇙ j₁) (true⇙ j₂)
true⇙ (fst j)      = fst (true⇙ j)
true⇙ (snd j)      = snd (true⇙ j)
true⇙ (up j)       = up (true⇙ j)
true⇙ (down j)     = down (true⇙ j)

true⇗⇙-id : ∀ {Γ k} {A : Ty k} (j : True Γ A) → true⇙ (true⇗ j) ≡ j
true⇗⇙-id (var x)      = refl
true⇗⇙-id (lam j)      = cong lam (true⇗⇙-id j)
true⇗⇙-id (app j₁ j₂)  = cong₂ app (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (pair j₁ j₂) = cong₂ pair (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (fst j)      = cong fst (true⇗⇙-id j)
true⇗⇙-id (snd j)      = cong snd (true⇗⇙-id j)
true⇗⇙-id (up j)       = cong up (true⇗⇙-id j)
true⇗⇙-id (down j)     = cong down (true⇗⇙-id j)

prov⇗ : ∀ {Γ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k n} (j : Prov Γ ts A) →
           Prov Γ (ᵗ⌊ j ⌋ ∷ ts) A
prov⇗ (var x)      = var x
prov⇗ (lam j)      = lam (prov⇗ j)
prov⇗ (app j₁ j₂)  = app (prov⇗ j₁) (prov⇗ j₂)
prov⇗ (pair j₁ j₂) = pair (prov⇗ j₁) (prov⇗ j₂)
prov⇗ (fst j)      = fst (prov⇗ j)
prov⇗ (snd j)      = snd (prov⇗ j)
prov⇗ (up j)       = up (prov⇗ j)
prov⇗ (down j)     = down (prov⇗ j)

prov⇙ : ∀ {Γ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k (suc n)} (j : Prov Γ ts A) →
           Prov Γ (tail ts) A
prov⇙ (var x)                        = var x
prov⇙ (lam {ts = ts} j)              rewrite tail-LAMs ts = lam (prov⇙ j)
prov⇙ (app {ts₁ = ts₁} {ts₂} j₁ j₂)  rewrite tail-APPs ts₁ ts₂ = app (prov⇙ j₁) (prov⇙ j₂)
prov⇙ (pair {ts₁ = ts₁} {ts₂} j₁ j₂) rewrite tail-PAIRs ts₁ ts₂ = pair (prov⇙ j₁) (prov⇙ j₂)
prov⇙ (fst {ts = ts}j)               rewrite tail-FSTs ts = fst (prov⇙ j)
prov⇙ (snd {ts = ts}j)               rewrite tail-SNDs ts = snd (prov⇙ j)
prov⇙ (up {ts = ts}j)                rewrite tail-UPs ts = up (prov⇙ j)
prov⇙ (down {ts = ts}j)              rewrite tail-DOWNs ts = down (prov⇙ j)

prov⇗⇙-id : ∀ {Γ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k n} (j : Prov Γ ts A) →
                prov⇙ (prov⇗ j) ≡ j
prov⇗⇙-id (var x)      = refl
prov⇗⇙-id (lam j)      = cong lam (prov⇗⇙-id j)
prov⇗⇙-id (app j₁ j₂)  = cong₂ app (prov⇗⇙-id j₁) (prov⇗⇙-id j₂)
prov⇗⇙-id (pair j₁ j₂) = cong₂ pair (prov⇗⇙-id j₁) (prov⇗⇙-id j₂)
prov⇗⇙-id (fst j)      = cong fst (prov⇗⇙-id j)
prov⇗⇙-id (snd j)      = cong snd (prov⇗⇙-id j)
prov⇗⇙-id (up j)       = cong up (prov⇗⇙-id j)
prov⇗⇙-id (down j)     = cong down (prov⇗⇙-id j)

--prov⋘ : ∀ {Γ k n} {A : Ty (suc k)} {ts : Vec ᵍ⌊ Γ ⌋ (suc k) n} (j : Prov Γ ts A) →
--           Prov Γ (ts ‘ init A)
--prov⋘ = ?



_∴_ : ∀ {Γ k n} (ts : Vec ᵍ⌊ Γ ⌋ k n) (A : Ty k) → Ty (n + k)
[]       ∴ A = A
(t ∷ ts) ∴ A = t ∶ (ts ∴ A)

infixr 15 _∴_

--D : ∀

-- ren-prov : ∀ {Γ Γ′ k n} {A : Ty k} {ts : Vec ᵍ⌊ Γ ⌋ k n} (η : Γ′ ⊇ Γ) → Prov Γ ts A →
--              Prov Γ′ (ren-vec ʰ⌊ η ⌋ ts) A
-- ren-prov η (var x)                = ? --rewrite ren-VARs ʰ⌊ η ⌋ ⁱ⌊ x ⌋ |
--                                         --       °ren-fin-var η x =
--                                          --var (ren-var η x)
-- ren-prov η (lam {ts} j)           rewrite ren-LAMs ʰ⌊ η ⌋ ts =
--                                          lam (ren-prov (lift η) j)
-- ren-prov η (app {ts} {us} j₁ j₂)  rewrite ren-APPs ʰ⌊ η ⌋ ts us =
--                                          app (ren-prov η j₁) (ren-prov η j₂)
-- ren-prov η (pair {ts} {us} j₁ j₂) rewrite ren-PAIRs ʰ⌊ η ⌋ ts us =
--                                          pair (ren-prov η j₁) (ren-prov η j₂)
-- ren-prov η (fst {ts} j)           rewrite ren-FSTs ʰ⌊ η ⌋ ts =
--                                          fst (ren-prov η j)
-- ren-prov η (snd {ts} j)           rewrite ren-SNDs ʰ⌊ η ⌋ ts =
--                                          snd (ren-prov η j)
-- ren-prov η (up {ts} j)            = ? --rewrite ren-UPs ʰ⌊ η ⌋ ts =
--                                         -- up (ren-prov η j)
-- ren-prov η (down {ts} j)          = ? --rewrite ren-DOWNs ʰ⌊ η ⌋ ts =
--                                         -- down (ren-prov η j)

-- wk-prov : ∀ {Γ n A C} {ts : Vec ᵍ⌊ Γ ⌋ n} → Prov Γ ts C →
--               Prov (Γ , A) (wk-vec ts) C
-- wk-prov {Γ} rewrite sym (°id Γ) = ren-prov ⊇wk

-- wk*-prov : ∀ {Γ n C} {ts : Vec 0 n} → Prov ∅ ts C →
--                Prov Γ (wk*-vec ts) C
-- wk*-prov {Γ} rewrite sym (°to Γ) = ren-prov ⊇to

-- v₀ : ∀ {Γ k} {A : Ty k} → Prov (Γ , A) (VARs i₀) A
-- v₀ = var x₀

-- v₁ : ∀ {Γ k} {A B : Ty k} → Prov ((Γ , A) , B) (VARs i₁) A
-- v₁ = var x₁

-- v₂ : ∀ {Γ k} {A B C : Ty k} → Prov (((Γ , A) , B) , C) (VARs i₂) A
-- v₂ = var x₂

-- -- I[_] : ∀ {Γ} n {A} → Prov Γ (LAMs (VARs i₀)) (A ⊃ A)
-- -- I = lam v₀

-- -- K[_] : ∀ {Γ} n {A B} → Prov Γ (LAMs (LAMs (VARs i₁))) (A ⊃ B ⊃ A)
-- -- K = lam (lam v₁)

-- -- S[_] : ∀ {Γ} n {A B C} →
-- --          Prov Γ (LAMs (LAMs (LAMs
-- --                     (APPs (APPs (VARs i₂) (VARs i₀))
-- --                                (APPs (VARs i₁) (VARs i₀))))))
-- --                 ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
-- -- S = lam (lam (lam
-- --            (app (app v₂ v₀)
-- --                      (app v₁ v₀))))

-- -- I≡I[0] : ∀ {Γ A} → true⇒ (I {Γ} {A}) ≡ I[ 0 ]
-- -- I≡I[0] = refl

-- -- ⇗I≡I[1] : ∀ {Γ A} → true⇗ (I {Γ} {A}) ≡ I[ 1 ]
-- -- ⇗I≡I[1] = refl

-- -- ⇗⇗I≡I[2] : ∀ {Γ A} → prov⇗ (true⇗ (I {Γ} {A})) ≡ I[ 2 ]
-- -- ⇗⇗I≡I[2] = refl
