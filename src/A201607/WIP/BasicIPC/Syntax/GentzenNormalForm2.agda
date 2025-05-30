{-# OPTIONS --sized-types #-}

module A201607.WIP.BasicIPC.Syntax.GentzenNormalForm2 where

open import A201607.BasicIPC.Syntax.GentzenNormalForm public


data NfNe⁼ {A Γ} (t : Γ ⊢ A) : Set where
  nfⁿᶠⁿᵉ⁼ : (t′ : Γ ⊢ⁿᶠ A) → {{_ : nf→tm t′ ≡ t}} → NfNe⁼ t
  neⁿᶠⁿᵉ⁼ : (t′ : Γ ⊢ⁿᵉ A) → {{_ : ne→tm t′ ≡ t}} → NfNe⁼ t


mutual
  data Nf {Γ} : ∀ {A} → Γ ⊢ A → Set where
    neⁿᶠ   : ∀ {A} {t : Γ ⊢ A} → Ne t → Nf t
    lamⁿᶠ  : ∀ {A B} {t : Γ , A ⊢ B} → Nf t → Nf (lam t)
    pairⁿᶠ : ∀ {A B} {t : Γ ⊢ A} {u : Γ ⊢ B} → Nf t → Nf u → Nf (pair t u)
    unitⁿᶠ : Nf unit

  data Ne {Γ} : ∀ {A} → Γ ⊢ A → Set where
    varⁿᵉ : ∀ {A} → (i : A ∈ Γ) → Ne (var i)
    appⁿᵉ : ∀ {A B} {t : Γ ⊢ A ▻ B} {u : Γ ⊢ A} → Ne t → Nf u → Ne (app t u)
    fstⁿᵉ : ∀ {A B} {t : Γ ⊢ A ∧ B} → Ne t → Ne (fst t)
    sndⁿᵉ : ∀ {A B} {t : Γ ⊢ A ∧ B} → Ne t → Ne (snd t)

data NfNe {A Γ} (t : Γ ⊢ A) : Set where
  nfⁿᶠⁿᵉ : Nf t → NfNe t
  neⁿᶠⁿᵉ : Ne t → NfNe t


mutual
  expⁿᶠ : ∀ {A Γ} {t : Γ ⊢ A} → Nf t → Σ (Γ ⊢ⁿᶠ A) (λ t′ → nf→tm t′ ≡ t)
  expⁿᶠ (neⁿᶠ d)     with expⁿᵉ d
  expⁿᶠ (neⁿᶠ d)     | t′ , refl = neⁿᶠ t′ , refl
  expⁿᶠ (lamⁿᶠ d)    with expⁿᶠ d
  expⁿᶠ (lamⁿᶠ d)    | t′ , refl = lamⁿᶠ t′ , refl
  expⁿᶠ (pairⁿᶠ d e) with expⁿᶠ d | expⁿᶠ e
  expⁿᶠ (pairⁿᶠ d e) | t′ , refl | u′ , refl = pairⁿᶠ t′ u′ , refl
  expⁿᶠ unitⁿᶠ       = unitⁿᶠ , refl

  expⁿᵉ : ∀ {A Γ} {t : Γ ⊢ A} → Ne t → Σ (Γ ⊢ⁿᵉ A) (λ t′ → ne→tm t′ ≡ t)
  expⁿᵉ (varⁿᵉ i)   = varⁿᵉ i , refl
  expⁿᵉ (appⁿᵉ d e) with expⁿᵉ d | expⁿᶠ e
  expⁿᵉ (appⁿᵉ d e) | t′ , refl | u′ , refl = appⁿᵉ t′ u′ , refl
  expⁿᵉ (fstⁿᵉ d)   with expⁿᵉ d
  expⁿᵉ (fstⁿᵉ d)   | t′ , refl = fstⁿᵉ t′ , refl
  expⁿᵉ (sndⁿᵉ d)   with expⁿᵉ d
  expⁿᵉ (sndⁿᵉ d)   | t′ , refl = sndⁿᵉ t′ , refl

expⁿᶠⁿᵉ : ∀ {A Γ} {t : Γ ⊢ A} → NfNe t → NfNe⁼ t
expⁿᶠⁿᵉ (nfⁿᶠⁿᵉ d) with expⁿᶠ d
expⁿᶠⁿᵉ (nfⁿᶠⁿᵉ d) | t′ , refl = nfⁿᶠⁿᵉ⁼ t′
expⁿᶠⁿᵉ (neⁿᶠⁿᵉ d) with expⁿᵉ d
expⁿᶠⁿᵉ (neⁿᶠⁿᵉ d) | t′ , refl = neⁿᶠⁿᵉ⁼ t′


mutual
  impⁿᶠ : ∀ {A Γ} {t : Γ ⊢ A} → (t′ : Γ ⊢ⁿᶠ A) → {{_ : nf→tm t′ ≡ t}} → Nf t
  impⁿᶠ (neⁿᶠ t′)      {{refl}} = neⁿᶠ (impⁿᵉ t′)
  impⁿᶠ (lamⁿᶠ t′)     {{refl}} = lamⁿᶠ (impⁿᶠ t′)
  impⁿᶠ (pairⁿᶠ t′ u′) {{refl}} = pairⁿᶠ (impⁿᶠ t′) (impⁿᶠ u′)
  impⁿᶠ unitⁿᶠ         {{refl}} = unitⁿᶠ

  impⁿᵉ : ∀ {A Γ} {t : Γ ⊢ A} → (t′ : Γ ⊢ⁿᵉ A) → {{_ : ne→tm t′ ≡ t}} → Ne t
  impⁿᵉ (varⁿᵉ i)     {{refl}} = varⁿᵉ i
  impⁿᵉ (appⁿᵉ t′ u′) {{refl}} = appⁿᵉ (impⁿᵉ t′) (impⁿᶠ u′)
  impⁿᵉ (fstⁿᵉ t′)    {{refl}} = fstⁿᵉ (impⁿᵉ t′)
  impⁿᵉ (sndⁿᵉ t′)    {{refl}} = sndⁿᵉ (impⁿᵉ t′)

impⁿᶠⁿᵉ : ∀ {A Γ} {t : Γ ⊢ A} → NfNe⁼ t → NfNe t
impⁿᶠⁿᵉ (nfⁿᶠⁿᵉ⁼ d) = nfⁿᶠⁿᵉ (impⁿᶠ d)
impⁿᶠⁿᵉ (neⁿᶠⁿᵉ⁼ d) = neⁿᶠⁿᵉ (impⁿᵉ d)


nf : ∀ {A Γ} {t : Γ ⊢ A} → NfNe t → Nf t
nf (nfⁿᶠⁿᵉ d) = d
nf (neⁿᶠⁿᵉ d) = neⁿᶠ d


lamⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ , A ⊢ B} → NfNe t → NfNe (lam t)
lamⁿᶠⁿᵉ = nfⁿᶠⁿᵉ ∘ lamⁿᶠ ∘ nf

unlamⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ , A ⊢ B} → NfNe (lam t) → NfNe t
unlamⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ ()))
unlamⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (lamⁿᶠ t′)) = nfⁿᶠⁿᵉ t′
unlamⁿᶠⁿᵉ (neⁿᶠⁿᵉ ())


pairⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → NfNe t → NfNe u → NfNe (pair t u)
pairⁿᶠⁿᵉ (nfⁿᶠⁿᵉ t′) = nfⁿᶠⁿᵉ ∘ pairⁿᶠ t′ ∘ nf
pairⁿᶠⁿᵉ (neⁿᶠⁿᵉ t′) = nfⁿᶠⁿᵉ ∘ pairⁿᶠ (neⁿᶠ t′) ∘ nf

unpairⁿᶠⁿᵉ₁ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → NfNe (pair t u) → NfNe t
unpairⁿᶠⁿᵉ₁ (nfⁿᶠⁿᵉ (neⁿᶠ ()))
unpairⁿᶠⁿᵉ₁ (nfⁿᶠⁿᵉ (pairⁿᶠ t′ u′)) = nfⁿᶠⁿᵉ t′
unpairⁿᶠⁿᵉ₁ (neⁿᶠⁿᵉ ())

unpairⁿᶠⁿᵉ₂ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → NfNe (pair t u) → NfNe u
unpairⁿᶠⁿᵉ₂ (nfⁿᶠⁿᵉ (neⁿᶠ ()))
unpairⁿᶠⁿᵉ₂ (nfⁿᶠⁿᵉ (pairⁿᶠ t′ u′)) = nfⁿᶠⁿᵉ u′
unpairⁿᶠⁿᵉ₂ (neⁿᶠⁿᵉ ())

pairⁿᶠⁿᵉ′ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → NfNe t × NfNe u → NfNe (pair t u)
pairⁿᶠⁿᵉ′ (d , e) = pairⁿᶠⁿᵉ d e

unpairⁿᶠⁿᵉ′ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → NfNe (pair t u) → NfNe t × NfNe u
unpairⁿᶠⁿᵉ′ d = unpairⁿᶠⁿᵉ₁ d , unpairⁿᶠⁿᵉ₂ d


appⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A ▻ B} {u : Γ ⊢ A} → Ne t → NfNe u → NfNe (app t u)
appⁿᶠⁿᵉ t′ = neⁿᶠⁿᵉ ∘ appⁿᵉ t′ ∘ nf

unappⁿᶠⁿᵉ₁ : ∀ {A B Γ} {t : Γ ⊢ A ▻ B} {u : Γ ⊢ A} → NfNe (app t u) → NfNe t
unappⁿᶠⁿᵉ₁ (nfⁿᶠⁿᵉ (neⁿᶠ (appⁿᵉ t′ u′))) = neⁿᶠⁿᵉ t′
unappⁿᶠⁿᵉ₁ (neⁿᶠⁿᵉ (appⁿᵉ t′ u′))        = neⁿᶠⁿᵉ t′

unappⁿᶠⁿᵉ₂ : ∀ {A B Γ} {t : Γ ⊢ A ▻ B} {u : Γ ⊢ A} → NfNe (app t u) → NfNe u
unappⁿᶠⁿᵉ₂ (nfⁿᶠⁿᵉ (neⁿᶠ (appⁿᵉ t′ u′))) = nfⁿᶠⁿᵉ u′
unappⁿᶠⁿᵉ₂ (neⁿᶠⁿᵉ (appⁿᵉ t′ u′))        = nfⁿᶠⁿᵉ u′


unfstⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A ∧ B} → NfNe (fst t) → NfNe t
unfstⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ (fstⁿᵉ t′))) = neⁿᶠⁿᵉ t′
unfstⁿᶠⁿᵉ (neⁿᶠⁿᵉ (fstⁿᵉ t′))        = neⁿᶠⁿᵉ t′

unsndⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A ∧ B} → NfNe (snd t) → NfNe t
unsndⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ (sndⁿᵉ t′))) = neⁿᶠⁿᵉ t′
unsndⁿᶠⁿᵉ (neⁿᶠⁿᵉ (sndⁿᵉ t′))        = neⁿᶠⁿᵉ t′


¬applamⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A} → Not (NfNe (app (lam t) u))
¬applamⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ (appⁿᵉ () _)))
¬applamⁿᶠⁿᵉ (neⁿᶠⁿᵉ (appⁿᵉ () _))

¬fstpairⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → Not (NfNe (fst (pair t u)))
¬fstpairⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ (fstⁿᵉ ())))
¬fstpairⁿᶠⁿᵉ (neⁿᶠⁿᵉ (fstⁿᵉ ()))

¬sndpairⁿᶠⁿᵉ : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B} → Not (NfNe (snd (pair t u)))
¬sndpairⁿᶠⁿᵉ (nfⁿᶠⁿᵉ (neⁿᶠ (sndⁿᵉ ())))
¬sndpairⁿᶠⁿᵉ (neⁿᶠⁿᵉ (sndⁿᵉ ()))


×Dec : ∀ {p q} {P : Set p} {Q : Set q} → Dec P → Dec Q → Dec (P × Q)
×Dec (yes x) (yes y) = yes (x , y)
×Dec (no ¬x) _       = no (¬x ∘ π₁)
×Dec _       (no ¬y) = no (¬y ∘ π₂)


nfne? : ∀ {A Γ} → (t : Γ ⊢ A) → Dec (NfNe t)
nfne? (var i)    = yes (neⁿᶠⁿᵉ (varⁿᵉ i))
nfne? (lam t)    = mapDec lamⁿᶠⁿᵉ unlamⁿᶠⁿᵉ (nfne? t)
nfne? (app t u)  with nfne? t
nfne? (app t u)  | yes (nfⁿᶠⁿᵉ (neⁿᶠ t′))  = mapDec (appⁿᶠⁿᵉ t′) unappⁿᶠⁿᵉ₂ (nfne? u)
nfne? (app _ u)  | yes (nfⁿᶠⁿᵉ (lamⁿᶠ t′)) = no ¬applamⁿᶠⁿᵉ
nfne? (app t u)  | yes (neⁿᶠⁿᵉ t′)         = mapDec (appⁿᶠⁿᵉ t′) unappⁿᶠⁿᵉ₂ (nfne? u)
nfne? (app t u)  | no  ¬nfne               = no (¬nfne ∘ unappⁿᶠⁿᵉ₁)
nfne? (pair t u) = mapDec pairⁿᶠⁿᵉ′ unpairⁿᶠⁿᵉ′ (×Dec (nfne? t) (nfne? u))
nfne? (fst t)    with nfne? t
nfne? (fst t)    | yes (nfⁿᶠⁿᵉ (neⁿᶠ t′))      = yes (neⁿᶠⁿᵉ (fstⁿᵉ t′))
nfne? (fst _)    | yes (nfⁿᶠⁿᵉ (pairⁿᶠ t′ u′)) = no ¬fstpairⁿᶠⁿᵉ
nfne? (fst t)    | yes (neⁿᶠⁿᵉ t′)             = yes (neⁿᶠⁿᵉ (fstⁿᵉ t′))
nfne? (fst t)    | no  ¬nfne                   = no (¬nfne ∘ unfstⁿᶠⁿᵉ)
nfne? (snd t)    with nfne? t
nfne? (snd t)    | yes (nfⁿᶠⁿᵉ (neⁿᶠ t′))      = yes (neⁿᶠⁿᵉ (sndⁿᵉ t′))
nfne? (snd _)    | yes (nfⁿᶠⁿᵉ (pairⁿᶠ t′ u′)) = no ¬sndpairⁿᶠⁿᵉ
nfne? (snd t)    | yes (neⁿᶠⁿᵉ t′)             = yes (neⁿᶠⁿᵉ (sndⁿᵉ t′))
nfne? (snd t)    | no  ¬nfne                   = no (¬nfne ∘ unsndⁿᶠⁿᵉ)
nfne? unit       = yes (nfⁿᶠⁿᵉ unitⁿᶠ)
