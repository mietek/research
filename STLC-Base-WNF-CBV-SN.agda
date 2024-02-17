----------------------------------------------------------------------------------------------------

-- strong normalization for closed terms, after Ahmed
-- TODO: needs a lot of work

module STLC-Base-WNF-CBV-SN where

open import STLC-Base-WNF-CBV public


----------------------------------------------------------------------------------------------------

mutual
  HWN : ∀ {Γ A} → Γ ⊢ A → Set
  HWN t = WN t × HWN! t

  HWN! : ∀ {A Γ} → Γ ⊢ A → Set
  HWN! {⌜◦⌝}     t  = 𝟙
  HWN! {A ⌜⊃⌝ B} t₁ = ∀ {t₂} → HWN t₂ → HWN (t₁ ⌜$⌝ t₂)

mutual
  stepHWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN t′ → HWN t
  stepHWN r (wn′ , hwn!′) = stepWN r wn′ , stepHWN! r hwn!′

  stepHWN! : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN! t′ → HWN! t
  stepHWN! {⌜◦⌝}     r unit       = unit
  stepHWN! {A ⌜⊃⌝ B} r f    hwn₂′ = stepHWN (cong$₁ r) (f hwn₂′)

step⇒*HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → HWN t′ → HWN t
step⇒*HWN done        hwn′ = hwn′
step⇒*HWN (step r rs) hwn′ = stepHWN r (step⇒*HWN rs hwn′)

step⇓HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇓ t′ → HWN t′ → HWN t
step⇓HWN = step⇒*HWN ∘ fst

mutual
  skipHWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN t → HWN t′
  skipHWN r (wn , hwn!) = skipWN r wn , skipHWN! r hwn!

  skipHWN! : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → HWN! t → HWN! t′
  skipHWN! {⌜◦⌝}     r unit      = unit
  skipHWN! {A ⌜⊃⌝ B} r f    hwn₂ = skipHWN (cong$₁ r) (f hwn₂)

skip⇒*HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → HWN t → HWN t′
skip⇒*HWN done        hwn = hwn
skip⇒*HWN (step r rs) hwn = skip⇒*HWN rs (skipHWN r hwn)

skip⇓HWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇓ t′ → HWN t → HWN t′
skip⇓HWN = skip⇒*HWN ∘ fst


----------------------------------------------------------------------------------------------------

-- looks almost like half of subcut, but the contexts don’t match
-- subcut : ∀ {Γ Ξ A B} (σ : Ξ ⊢* Γ) (t₁ : (A ∷ Γ) ⊢ B) (t₂ : Γ ⊢ A) →
--          sub (lift§ σ) t₁ [ sub σ t₂ ] ≡ sub σ (t₁ [ t₂ ])
lem₀ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) (t₂ : Ξ ⊢ A) →
       (_[ t₂ ] ∘ sub (lift§ σ)) t₁ ≡ sub (σ , t₂) t₁
lem₀ σ t₁ t₂ = compsub (id§ , t₂) (lift§ σ) t₁ ⁻¹
             ⋮ (flip sub t₁ ∘ (_, t₂)) & ( eqsub§ id§ t₂ σ
                                         ⋮ lidsub§ σ
                                         )

lem₁ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
       ⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂ ⇒ sub (σ , t₂) t₁
lem₁ σ t₁ p₂ = βred⊃ (lem₀ σ t₁ _ ⁻¹) p₂

lem₂ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) {t′ : Ξ ⊢ B} →
       sub (σ , t₂) t₁ ⇓ t′ →
       ⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂ ⇓ t′
lem₂ σ t₁ p₂ (rs , p′) = (step (lem₁ σ t₁ p₂) rs) , p′

lem₃ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
       WN (sub (σ , t₂) t₁) →
       WN (⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂)
lem₃ σ t₁ p₂ (t′ , n) = t′ , lem₂ σ t₁ p₂ n

mutual
  lem₄ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
         HWN (sub (σ , t₂) t₁) →
         HWN (⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂)
  lem₄ σ t₁ p₂ (wn , hwn!) = lem₃ σ t₁ p₂ wn , lem₄! σ t₁ p₂ hwn!

  lem₄! : ∀ {B Γ Ξ A} (σ : Ξ ⊢§ Γ) (t₁ : Γ , A ⊢ B) {t₂ : Ξ ⊢ A} (p₂ : NF t₂) →
          HWN! (sub (σ , t₂) t₁) →
          HWN! (⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂)
  lem₄! {⌜◦⌝}       σ t₁ p₂ unit      = unit
  lem₄! {B₁ ⌜⊃⌝ B₂} σ t₁ p₂ f    hwn₂ = stepHWN (cong$₁ (lem₁ σ t₁ p₂)) (f hwn₂)


----------------------------------------------------------------------------------------------------

data HWN§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : HWN§ ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} (θ : HWN§ τ) (hwn : HWN t) → HWN§ (τ , t)

sub∋HWN : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} (θ : HWN§ σ) (i : Γ ∋ A) → HWN (sub∋ σ i)
sub∋HWN (θ , hwn) zero    = hwn
sub∋HWN (θ , hwn) (wk∋ i) = sub∋HWN θ i

mutual
  lem₅ : ∀ {Γ Ξ A B} (σ : Ξ ⊢§ Γ) (θ : HWN§ σ) (t₁ : Γ , A ⊢ B) (t₁′ : Ξ ⊢ A ⌜⊃⌝ B) {t₂ : Ξ ⊢ A} →
         HWN t₂ → HWN (⌜λ⌝ (sub (lift§ σ) t₁) ⌜$⌝ t₂)
  lem₅ σ θ t₁ t₁′ hwn₂@((t₂′ , n₂@(rs₂ , p₂′)) , hwn!₂) =
    let hwn₂′ = skip⇓HWN n₂ hwn₂
      in step⇒*HWN (cong$₂⇒* ⌜λ⌝- rs₂) (lem₄ σ t₁ p₂′ (subHWN (σ , t₂′) (θ , hwn₂′) t₁))

  subHWN : ∀ {Γ Ξ A} (σ : Ξ ⊢§ Γ) (θ : HWN§ σ) (t : Γ ⊢ A) → HWN (sub σ t)
  subHWN σ θ (var i)     = sub∋HWN θ i
  subHWN σ θ (⌜λ⌝ t)     = let t′ = sub σ (⌜λ⌝ t)
                             in (t′ , done , ⌜λ⌝-) , λ {t₂} → lem₅ σ θ t t′ {t₂}
  subHWN σ θ (t₁ ⌜$⌝ t₂) = let wn , hwn! = subHWN σ θ t₁
                             in hwn! (subHWN σ θ t₂)

hwn : ∀ {A} (t : ∙ ⊢ A) → HWN t
hwn t = subst HWN (lidsub t) (subHWN ∙ ∙ t)

wn : ∀ {A} (t : ∙ ⊢ A) → WN t
wn = fst ∘ hwn


----------------------------------------------------------------------------------------------------

-- general shape of the definition due to Altenkirch
-- TODO: this specific definition is probably wrong, as it uses the CBV reduction strategy
data SN {Γ A} (t : Γ ⊢ A) : Set where
  make : ∀ (h : ∀ {t′} → t ⇒ t′ → SN t′) → SN t

recSN : ∀ {𝓍} (X : ∀ {Γ A} → Γ ⊢ A → Set 𝓍) {Γ A} {t : Γ ⊢ A} → SN t →
          (∀ {t} → (∀ {t′} → t ⇒ t′ → X t′) → X t) →
        X t
recSN X (make h) f = f λ r → recSN X (h r) f

SN→WN : ∀ {Γ A} {t : Γ ⊢ A} → SN t → WN t
SN→WN sn = recSN WN sn aux
  where
    aux : ∀ {t} → (∀ {t′} → t ⇒ t′ → WN t′) → WN t
    aux {t} h with prog⇒ t
    ... | done p = _ , done , p
    ... | step r = let _ , rs , p′ = h r
                     in _ , step r rs , p′

WN→SN : ∀ {Γ A} {t : Γ ⊢ A} → WN t → SN t
WN→SN (t′ , done , p′)      = make λ r → r ↯ NF→¬R p′
WN→SN (t′ , step r rs , p′) = make λ r′ → subst SN (det⇒ r r′) (WN→SN (t′ , rs , p′))

sn : ∀ {A} (t : ∙ ⊢ A) → SN t
sn = WN→SN ∘ wn


----------------------------------------------------------------------------------------------------
