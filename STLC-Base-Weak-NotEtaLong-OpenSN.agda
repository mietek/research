module STLC-Base-Weak-NotEtaLong-OpenSN where

open import STLC-Base-Weak-NotEtaLong public
open import STLC-Base-Properties public


----------------------------------------------------------------------------------------------------

cong$₁⇒* : ∀ {Γ A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} → t₁ ⇒* t₁′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁′ ⌜$⌝ t₂
cong$₁⇒* done        = done
cong$₁⇒* (step r rs) = step (cong$₁ r) (cong$₁⇒* rs)

cong$₂⇒* : ∀ {Γ A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} → NF t₁ → t₂ ⇒* t₂′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁ ⌜$⌝ t₂′
cong$₂⇒* p₁ done        = done
cong$₂⇒* p₁ (step r rs) = step (cong$₂ p₁ r) (cong$₂⇒* p₁ rs)


----------------------------------------------------------------------------------------------------

-- iterated reduction to NF
infix 4 _⇓_
_⇓_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
t ⇓ t′ = t ⇒* t′ × NF t′

step⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t′ ⇓ t″ → t ⇓ t″
step⇓ r (rs′ , p″) = step r rs′ , p″

skip⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇓ t″ → t′ ⇓ t″
skip⇓ r (rs′ , p″) = skip⇒* r rs′ p″ , p″

-- determinism
det⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇓ t′ → t ⇓ t″ → t′ ≡ t″
det⇓ (rs , p′) (rs′ , p″) = det⇒* rs p′ rs′ p″

-- uniqueness of proofs
uni⇓ : ∀ {Γ A} {t t′ : Γ ⊢ A} (n n′ : t ⇓ t′) → n ≡ n′
uni⇓ (rs , p′) (rs′ , p″) = _,_ & uni⇒* rs rs′ p′ ⊗ uniNF p′ p″


----------------------------------------------------------------------------------------------------

-- weak normalization
WN : ∀ {Γ A} → Γ ⊢ A → Set
WN t = Σ _ λ t′ → t ⇓ t′

stepWN : ∀ {Γ A} {t t′ :  Γ ⊢ A} → t ⇒ t′ → WN t′ → WN t
stepWN r (t″ , n′) = t″ , step⇓ r n′

skipWN : ∀ {Γ A} {t t′ :  Γ ⊢ A} → t ⇒ t′ → WN t → WN t′
skipWN r (t″ , n′) = t″ , skip⇓ r n′


----------------------------------------------------------------------------------------------------

lemren⇒ : ∀ {Γ Γ′ A B} (e : Γ ⊆ Γ′) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           (_[ ren⊢ e t₂ ] ∘ ren⊢ (keep e)) t₁ ≡ (ren⊢ e ∘ _[ t₂ ]) t₁
lemren⇒ e t₁ t₂ = eqsubren⊢ (ren⊢ e t₂ ∷ refl⊢*) (keep e) t₁ ⁻¹
                 ⋮ (flip sub⊢ t₁ ∘ (ren⊢ e t₂ ∷_)) & ( ridget⊢* e
                                                       ⋮ ridren⊢* e ⁻¹
                                                       )
                 ⋮ eqrensub⊢ e (t₂ ∷ refl⊢*) t₁

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒ t′ → ren⊢ e t ⇒ ren⊢ e t′
ren⇒ e (cong$₁ r₁)               = cong$₁ (ren⇒ e r₁)
ren⇒ e (cong$₂ p₁ r₂)            = cong$₂ (renNF e p₁) (ren⇒ e r₂)
ren⇒ e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (lemren⇒ e t₁ _ ⁻¹) (renNF e p₂)

ren⇒* : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒* t′ → ren⊢ e t ⇒* ren⊢ e t′
ren⇒* e done        = done
ren⇒* e (step r rs) = step (ren⇒ e r) (ren⇒* e rs)

ren⇓ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇓ t′ → ren⊢ e t ⇓ ren⊢ e t′
ren⇓ e (rs , p′) = ren⇒* e rs , renNF e p′

renWN : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → WN t → WN (ren⊢ e t)
renWN e (t′ , n) = ren⊢ e t′ , ren⇓ e n


----------------------------------------------------------------------------------------------------

-- data NF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
--   [] : NF* []
--   _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NF t → NF* ts → NF* (t ∷ ts)

-- TODO
open ≡-Reasoning

data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  [] : NNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)

-- TODO
sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → NNF* ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

-- substitution
mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NF t → NF (sub⊢ ss t)
  subNF ps ⌜λ⌝-    = ⌜λ⌝-
  subNF ps (nnf p) = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NNF t → NNF (sub⊢ ss t)
  subNNF ps ⌜v⌝-        = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂) = subNNF ps p₁ ⌜$⌝ subNF ps p₂

lemsub⇒ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Γ ⊢ A) →
           (_[ sub⊢ ss t₂ ] ∘ sub⊢ (lift⊢* ss)) t₁ ≡ (sub⊢ ss ∘ _[ t₂ ]) t₁
lemsub⇒ ss t₁ t₂ =
    begin
      (sub⊢ (sub⊢ ss t₂ ∷ id⊢*) ∘ sub⊢ (lift⊢* ss)) t₁
    ≡˘⟨ compsub⊢ (sub⊢ ss t₂ ∷ id⊢*) (lift⊢* ss) t₁ ⟩
      sub⊢ (sub⊢* (sub⊢ ss t₂ ∷ id⊢*) (lift⊢* ss)) t₁
    ≡⟨ (flip sub⊢ t₁ ∘ (sub⊢ ss t₂ ∷_)) & (
        begin
          (sub⊢* (sub⊢ ss t₂ ∷ id⊢*) ∘ weak⊢*) ss
        ≡˘⟨ eqsubren⊢* (sub⊢ ss t₂ ∷ id⊢*) (drop id⊆) ss ⟩
          sub⊢* (get⊢* (drop id⊆) (sub⊢ ss t₂ ∷ id⊢*)) ss
        ≡⟨⟩
          sub⊢* (get⊢* id⊆ id⊢*) ss
        ≡⟨ flip sub⊢* ss & lidget⊢* id⊢* ⟩
          sub⊢* id⊢* ss
        ≡⟨ lidsub⊢* ss ⟩
          ss
        ≡˘⟨ ridsub⊢* ss ⟩
          sub⊢* ss id⊢*
        ∎) ⟩
      sub⊢ (sub⊢* ss (t₂ ∷ id⊢*)) t₁
    ≡⟨ compsub⊢ ss (t₂ ∷ id⊢*) t₁ ⟩
      (sub⊢ ss ∘ sub⊢ (t₂ ∷ id⊢*)) t₁
    ∎

-- substitutivity
sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → NNF* ss → t ⇒ t′ → sub⊢ ss t ⇒ sub⊢ ss t′
sub⇒ ps (cong$₁ r₁)               = cong$₁ (sub⇒ ps r₁)
sub⇒ ps (cong$₂ p₁ r₂)            = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
sub⇒ ps (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (lemsub⇒ _ t₁ _ ⁻¹) (subNF ps p₂)


----------------------------------------------------------------------------------------------------

-- hereditary weak normalization
mutual
  HWN : ∀ {Γ A} → Γ ⊢ A → Set
  HWN t = WN t × HWN! t

  HWN! : ∀ {Γ A} → Γ ⊢ A → Set
  HWN!     {A = ⌜◦⌝}     t  = 𝟙
  HWN! {Γ} {A = A ⌜⊃⌝ B} t₁ = ∀ {Γ′ t₂} (e : Γ ⊆ Γ′) → HWN (ren⊢ e t₂) → HWN (ren⊢ e (t₁ ⌜$⌝ t₂))

mutual
  stepHWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN t′ → HWN t
  stepHWN r (wn′ , hwn!′) = stepWN r wn′ , stepHWN! r hwn!′

  stepHWN! : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN! t′ → HWN! t
  stepHWN! {A = ⌜◦⌝}          r unit         = unit
  stepHWN! {A = A ⌜⊃⌝ B} {t₁} r f    e hwn₂′ = stepHWN (cong$₁ (ren⇒ e r)) (f e hwn₂′)

step⇒*HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → HWN t′ → HWN t
step⇒*HWN done        hwn′ = hwn′
step⇒*HWN (step r rs) hwn′ = stepHWN r (step⇒*HWN rs hwn′)

step⇓HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇓ t′ → HWN t′ → HWN t
step⇓HWN = step⇒*HWN ∘ proj₁

mutual
  skipHWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN t → HWN t′
  skipHWN r (wn , hwn!) = skipWN r wn , skipHWN! r hwn!

  skipHWN! : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN! t → HWN! t′
  skipHWN! {A = ⌜◦⌝}     r unit        = unit
  skipHWN! {A = A ⌜⊃⌝ B} r f    e hwn₂ = skipHWN (cong$₁ (ren⇒ e r)) (f e hwn₂)

skip⇒*HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → HWN t → HWN t′
skip⇒*HWN done        hwn = hwn
skip⇒*HWN (step r rs) hwn = skip⇒*HWN rs (skipHWN r hwn)

skip⇓HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇓ t′ → HWN t → HWN t′
skip⇓HWN = skip⇒*HWN ∘ proj₁


----------------------------------------------------------------------------------------------------


-- mutual
--   renHWN : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → HWN t → HWN (ren⊢ e t)
--   renHWN e (wn@(t′ , rs , p′) , hwn!) = renWN e wn , renHWN! e hwn!

--   renHWN! : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → HWN! t → HWN! (ren⊢ e t)
--   renHWN! {A = ⌜◦⌝}          e unit           = unit
--   renHWN! {A = A ⌜⊃⌝ B} {t₁} e f {t₂} e′ hwn₂@(wn₂@(t₂′ , n₂@(rs₂ , p₂′)) , hwn!₂) =
--     {!!}

-- -- --     let z : HWN (ren⊢ e t₁ ⌜$⌝ t₂)
-- -- --         z = {!!}
-- -- --     in {!!} -- renHWN e (({!!} , ({!!} , {!!})) , {!!}) in {!!}
-- -- -- --    ((ren⊢ e t₁ ⌜$⌝ t₂′) , cong$₂⇒* {!!} rs₂ , {!!}) ,
-- -- -- --    {!!}


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- data HWN* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
-- -- --   []  : HWN* []
-- -- --   _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → HWN t → HWN* ts → HWN* (t ∷ ts)

-- -- -- {-

-- -- --       ren⊢* : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
-- -- --       ren⊢* e []       = []
-- -- --       ren⊢* e (t ∷ ts) = ren⊢ e t ∷ ren⊢* e ts

-- -- --       weak⊢* : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* Δ

-- -- -- -}

-- -- -- postulate
-- -- --   lem₋₁ : ∀ {Γ A} → weak⊢* {Γ} {Γ} {A} (refl⊢* {Γ = Γ}) ≡ {!refl⊢* {Γ = A ∷ Γ}!}

-- -- -- mutual
-- -- --   hmm : ∀ {Γ A} → HWN {A ∷ Γ} {A} (⌜v⌝ zero)
-- -- --   hmm = (⌜v⌝ zero , done , nnf ⌜v⌝-) , hmm!

-- -- --   hmm! : ∀ {Γ A} → HWN! {A ∷ Γ} {A} (⌜v⌝ zero)
-- -- --   hmm! {A = ⌜◦⌝}                                = unit
-- -- --   hmm! {A = A ⌜⊃⌝ B} ((t₂′ , rs , p₂′) , hwn!₂) =
-- -- --     (⌜v⌝ zero ⌜$⌝ t₂′ , cong$₂⇒* (nnf ⌜v⌝-) rs , nnf (⌜v⌝- ⌜$⌝ p₂′)) ,
-- -- --     {!!}


-- -- -- refl⊢*HWN* : ∀ {Γ} → HWN* {Γ} refl⊢*
-- -- -- refl⊢*HWN* {[]}    = []
-- -- -- refl⊢*HWN* {A ∷ Γ} = hmm ∷ {!refl⊢*HWN* {A ∷ Γ}!}


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- lem₀ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) (t₂ : Ξ ⊢ A) →
-- -- --        (sub⊢ (t₂ ∷ id⊢*) ∘ sub⊢ (lift⊢* ss)) t₁ ≡ sub⊢ (t₂ ∷ ss) t₁
-- -- -- lem₀ ss t₁ t₂ = compsub⊢ (t₂ ∷ id⊢*) (lift⊢* ss) t₁ ⁻¹
-- -- --               ⋮ (flip sub⊢ t₁ ∘ (t₂ ∷_)) & ( eqsub⊢* t₂ id⊢* ss
-- -- --                                             ⋮ lidsub⊢* ss
-- -- --                                             )

-- -- -- lem₁ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
-- -- --        ⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂ ⇒ sub⊢ (t₂ ∷ ss) t₁
-- -- -- lem₁ ss t₁ p₂ = βred⊃ (sym (lem₀ ss t₁ _)) p₂

-- -- -- lem₂ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) {t′ : Ξ ⊢ B} →
-- -- --        sub⊢ (t₂ ∷ ss) t₁ ⇓ t′ →
-- -- --        ⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂ ⇓ t′
-- -- -- lem₂ ss t₁ p₂ (rs , p′) = (step (lem₁ ss t₁ p₂) rs) , p′

-- -- -- lem₃ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
-- -- --        WN (sub⊢ (t₂ ∷ ss) t₁) →
-- -- --        WN (⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂)
-- -- -- lem₃ ss t₁ p₂ (t′ , n) = t′ , lem₂ ss t₁ p₂ n

-- -- -- mutual
-- -- --   lem₄ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
-- -- --          HWN (sub⊢ (t₂ ∷ ss) t₁) →
-- -- --          HWN (⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂)
-- -- --   lem₄ ss t₁ p₂ (wn , hwn!) = lem₃ ss t₁ p₂ wn , lem₄! ss t₁ p₂ hwn!

-- -- --   lem₄! : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (t₁ : A ∷ Γ ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
-- -- --           HWN! (sub⊢ (t₂ ∷ ss) t₁) →
-- -- --           HWN! (⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂)
-- -- --   lem₄! {B = ⌜◦⌝}       ss t₁ p₂ unit      = unit
-- -- --   lem₄! {B = B₁ ⌜⊃⌝ B₂} ss t₁ p₂ f    hwn₂ = stepHWN (cong$₁ (lem₁ ss t₁ p₂)) (f hwn₂)

-- -- -- sub∋HWN : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} (hwns : HWN* ss) (i : Γ ∋ A) → HWN (sub∋ ss i)
-- -- -- sub∋HWN (hwn ∷ hwns) zero    = hwn
-- -- -- sub∋HWN (hwn ∷ hwns) (suc i) = sub∋HWN hwns i

-- -- -- mutual
-- -- --   lem₅ : ∀ {Γ Ξ A B} (ss : Ξ ⊢* Γ) (hwns : HWN* ss) (t₁ : A ∷ Γ ⊢ B) (t₁′ : Ξ ⊢ A ⌜⊃⌝ B) {t₂ : Ξ ⊢ A} →
-- -- --             HWN t₂ → HWN (⌜λ⌝ (sub⊢ (lift⊢* ss) t₁) ⌜$⌝ t₂)
-- -- --   lem₅ ss hwns t₁ t₁′ hwn₂@((t₂′ , n₂@(rs₂ , p₂′)) , hwn!₂) =
-- -- --     let hwn₂′ = skip⇓HWN n₂ hwn₂
-- -- --     in  step⇒*HWN (cong$₂⇒* ⌜λ⌝- rs₂) (lem₄ ss t₁ p₂′ (sub⊢HWN (t₂′ ∷ ss) (hwn₂′ ∷ hwns) t₁))

-- -- --   sub⊢HWN : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (hwns : HWN* ss) (t : Γ ⊢ A) → HWN (sub⊢ ss t)
-- -- --   sub⊢HWN ss hwns (⌜v⌝ i)     = sub∋HWN hwns i
-- -- --   sub⊢HWN ss hwns (⌜λ⌝ t)     = let t′ = sub⊢ ss (⌜λ⌝ t)
-- -- --                                  in (t′ , done , ⌜λ⌝-) , λ {t₂} → lem₅ ss hwns t t′ {t₂}
-- -- --   sub⊢HWN ss hwns (t₁ ⌜$⌝ t₂) = let wn , hwn! = sub⊢HWN ss hwns t₁
-- -- --                                  in  hwn! (sub⊢HWN ss hwns t₂)

-- -- -- hwn : ∀ {Γ A} (t : Γ ⊢ A) → HWN t
-- -- -- hwn t = subst HWN (idsub⊢ t) (sub⊢HWN refl⊢* refl⊢*HWN* t)

-- -- -- wn : ∀ {Γ A} (t : Γ ⊢ A) → WN t
-- -- -- wn = proj₁ ∘ hwn


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- strong normalization
-- -- -- data SN {Γ A} (t : Γ ⊢ A) : Set where
-- -- --   make : (∀ {t′} → t ⇒ t′ → SN t′) → SN t

-- -- -- recSN : ∀ {𝓍} (X : ∀ {Γ A} → Γ ⊢ A → Set 𝓍) {Γ A} {t : Γ ⊢ A} → SN t →
-- -- --           (∀ {t} → (∀ {t′} → t ⇒ t′ → X t′) → X t) →
-- -- --         X t
-- -- -- recSN X (make h) f = f λ r → recSN X (h r) f

-- -- -- SN→WN : ∀ {Γ A} {t : Γ ⊢ A} → SN t → WN t
-- -- -- SN→WN sn = recSN WN sn aux
-- -- --   where
-- -- --     aux : ∀ {t} → (∀ {t′} → t ⇒ t′ → WN t′) → WN t
-- -- --     aux {t} h with prog⇒ t
-- -- --     ... | done p = _ , done , p
-- -- --     ... | step r = let _ , rs , p′ = h r
-- -- --                    in  _ , step r rs , p′

-- -- -- WN→SN : ∀ {Γ A} {t : Γ ⊢ A} → WN t → SN t
-- -- -- WN→SN (t′ , done , p′)      = make λ r → r ↯ NF→¬R p′
-- -- -- WN→SN (t′ , step r rs , p′) = make λ r′ → subst SN (det⇒ r r′) (WN→SN (t′ , rs , p′))

-- -- -- sn : ∀ {A} (t : [] ⊢ A) → SN t
-- -- -- sn = WN→SN ∘ wn


-- -- -- ----------------------------------------------------------------------------------------------------
