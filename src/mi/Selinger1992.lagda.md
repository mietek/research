---
author:  P. Selinger
hauthor: Peter Selinger
year:    1992
title:   Friedman’s A-translation
lang:    en
card:
  - P. Selinger (1992)
  - '[Friedman’s A-translation
    ](https://www.mscs.dal.ca/~selinger/papers/friedman.pdf)'
  - Manuscript.
todo:
  - DOI missing
---

<style>
  pre {
    position: relative;
    left: 0;
    max-width: 100%;
    margin: 3.3rem 0 3.5rem 0;
  }
</style>


```
-- Mechanised by Miëtek Bak
-- thanks to András, Ambrus, ames, drvink, Jesper, ncf, and roconnor
-- first-order predicate logic with one sort (naturals) and one predicate (equality)
-- variant with first-order structures for renaming and substitution

{-# OPTIONS --rewriting #-}

module mi.Selinger1992 where

open import mi.FOL public


----------------------------------------------------------------------------------------------------

-- TODO: statement of theorem 1


----------------------------------------------------------------------------------------------------

-- lemma 2

lem2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → PA / Γ ⊢ A
lem2 (‵var i)                = ‵var i
lem2 (‵lam d)                = ‵lam (lem2 d)
lem2 (d ‵$ e)                = lem2 d ‵$ lem2 e
lem2 (‵pair d e)             = ‵pair (lem2 d) (lem2 e)
lem2 (‵fst d)                = ‵fst (lem2 d)
lem2 (‵snd d)                = ‵snd (lem2 d)
lem2 (‵left d)               = ‵left (lem2 d)
lem2 (‵right d)              = ‵right (lem2 d)
lem2 (‵either c d e)         = ‵either (lem2 c) (lem2 d) (lem2 e)
lem2 (‵all refl d)           = ‵all refl (lem2 d)
lem2 (‵unall t refl d)       = ‵unall t refl (lem2 d)
lem2 (‵ex t refl d)          = ‵ex t refl (lem2 d)
lem2 (‵letex refl refl d e)  = ‵letex refl refl (lem2 d) (lem2 e)
lem2 (‵abortHA d)            = ‵abort (lem2 d)
lem2 (‵magicPA d)            = ‵magicPA (lem2 d)
lem2 ‵refl                   = ‵refl
lem2 (‵sym d)                = ‵sym (lem2 d)
lem2 (‵trans d e)            = ‵trans (lem2 d) (lem2 e)
lem2 (‵cong f i refl refl d) = ‵cong f i refl refl (lem2 d)
lem2 ‵dis                    = ‵dis
lem2 (‵inj d)                = ‵inj (lem2 d)
lem2 (‵ind refl refl d e)    = ‵ind refl refl (lem2 d) (lem2 e)
lem2 (‵proj i refl)          = ‵proj i refl
lem2 (‵comp g φ refl)        = ‵comp g φ refl
lem2 (‵rec f g)              = ‵rec f g


----------------------------------------------------------------------------------------------------

-- quantifier-free formulas

data IsQFree {k} : Fm k → Set where
  _‵⊃_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵⊃ B)
  _‵∧_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∧ B)
  _‵∨_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∨ B)
  ‵⊥  : IsQFree ‵⊥
  _‵=_ : ∀ {t u} → IsQFree (t ‵= u)

-- TODO: lemma 3
-- module _ where
--   open =-Reasoning
--
--   lem3 : ∀ {Þ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ f →
--            Þ / Γ ⊢ A ‵⫗ ‵fun f (tab ‵var) ‵= 𝟘
--   lem3 (A ‵⊃ B) = {!!}
--   lem3 (A ‵∧ B) = {!!}
--   lem3 (A ‵∨ B) = {!!}
--   lem3 ‵⊥      = sig
--                     (ƒconst 1)
--                     (‵pair
--                       (‵lam (abort 0))
--                       (‵lam (‵dis ‵$ (‵lam goal) ‵$ 0)))
--                   where
--                     goal : ∀ {Þ k} {Γ : Fm§ k} →
--                              Þ / Γ , ‵fun (ƒconst 1) (tab ‵var) ‵= 𝟘 ⊢ 𝕊 𝟘 ‵= 𝟘
--                     goal = begin
--                              𝕊 𝟘
--                            =⟨⟩
--                              ‵fun suc (∙ , ‵fun zero ∙)
--                            =⟨ ‵cong suc zero refl refl
--                                  (begin
--                                    ‵fun zero ∙
--                                  =˘⟨ ‵comp zero ∙ refl ⟩
--                                    ‵fun (comp zero ∙) (tab ‵var)
--                                  ∎)
--                                ⟩
--                              ‵fun suc (∙ , ‵fun (comp zero ∙) (tab ‵var))
--                            =˘⟨ ‵comp suc ((∙ , comp zero ∙)) refl ⟩
--                              ‵fun (comp suc (∙ , comp zero ∙)) (tab ‵var)
--                            =⟨⟩
--                              ‵fun (ƒconst 1) (tab ‵var)
--                            =⟨ 0 ⟩
--                              𝟘
--                            ∎
--   lem3 (t ‵= u) = {!!}


----------------------------------------------------------------------------------------------------

-- Π⁰₂ class of formulas

-- TODO: definition of Π⁰₂
-- TODO: lemma 4


----------------------------------------------------------------------------------------------------

-- double negation translation

_° : ∀ {k} → Fm k → Fm k
(A ‵⊃ B) ° = A ° ‵⊃ B °
(A ‵∧ B) ° = A ° ‵∧ B °
(A ‵∨ B) ° = ‵¬ ‵¬ (A ° ‵∨ B °)
(‵∀ A)   ° = ‵∀ A °
(‵∃ A)   ° = ‵¬ ‵¬ (‵∃ A °)
‵⊥      ° = ‵⊥
(t ‵= u) ° = ‵¬ ‵¬ (t ‵= u)

_°§ : ∀ {k} → Fm§ k → Fm§ k
∙       °§ = ∙
(Γ , A) °§ = Γ °§ , A °

-- TODO: interactions between DNT and renaming/substitution
module _ where
  postulate
    TODO1 : ∀ {k} {A : Fm (suc k)} {t} → A ° [ t /0]Fm ≡ A [ t /0]Fm °
  -- TODO1 = {!!}

  postulate
    TODO2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / wkFm§ Γ °§ ⊢ A → Þ / wkFm§ (Γ °§) ⊢ A
  -- TODO2 = {!!}

  postulate
    TODO3 : ∀ {Þ k} {Γ : Fm§ k} {A t} → Þ / Γ ⊢ A [ t /0]Fm ° → Þ / Γ ⊢ A ° [ t /0]Fm
  -- TODO3 = {!!}

  postulate
    TODO4 : ∀ {Þ k} {Γ : Fm§ k} {A t} → Þ / Γ ⊢ ‵∀ (A ° ‵⊃ wkFm A [ t /1]Fm °) →
              Þ / Γ ⊢ ‵∀ (A ° ‵⊃ wkFm (A °) [ t /1]Fm)
  -- TODO4 = {!!}

  postulate
    TODO5 : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / wkFm§ Γ °§ , A ° ⊢ wkFm C ° →
              Þ / wkFm§ (Γ °§) , A ° ⊢ wkFm (C °)
  -- TODO5 = {!!}

-- TODO: lemma 5
module _ where
  open ⫗-Reasoning

  lem5-1 : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ° ‵⫗ A
  lem5-1 {A = A ‵⊃ B} = ‵cong⊃ lem5-1 lem5-1
  lem5-1 {A = A ‵∧ B} = ‵cong∧ lem5-1 lem5-1
  lem5-1 {A = A ‵∨ B} = begin
                          (A ‵∨ B) °
                        ⫗⟨ ‵dn ⟩
                          A ° ‵∨ B °
                        ⫗⟨ ‵cong∨ lem5-1 lem5-1 ⟩
                          A ‵∨ B
                        ∎
  lem5-1 {A = ‵∀ A}   = ‵cong∀ lem5-1
  lem5-1 {A = ‵∃ A}   = begin
                          (‵∃ A) °
                        ⫗⟨ ‵dn ⟩
                          ‵∃ A °
                        ⫗⟨ ‵cong∃ lem5-1 ⟩
                          ‵∃ A
                        ∎
  lem5-1 {A = ‵⊥}    = ⫗refl
  lem5-1 {A = t ‵= u} = ‵dn

lem5-2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ (A °) ‵⊃ A °
lem5-2 {A = A ‵⊃ B} = ‵lam (‵lam (lem5-2 ‵$ ‵lam
                         (2 ‵$ ‵lam
                           (1 ‵$ 0 ‵$ 2))))
lem5-2 {A = A ‵∧ B} = ‵lam (‵pair
                         (lem5-2 ‵$ ‵lam
                           (1 ‵$ ‵lam
                             (1 ‵$ ‵fst 0)))
                         (lem5-2 ‵$ ‵lam
                           (1 ‵$ ‵lam
                             (1 ‵$ ‵snd 0))))
lem5-2 {A = A ‵∨ B} = ‵lam (‵join 0)
lem5-2 {A = ‵∀ A}   = ‵lam (‵all refl (lem5-2 ‵$ ‵lam
                         (1 ‵$ ‵lam
                           (1 ‵$ ‵unall (‵tvar 0) (idcutFm (A °)) 0))))
lem5-2 {A = ‵∃ A}   = ‵lam (‵join 0)
lem5-2 {A = ‵⊥}    = ‵lam (0 ‵$ ⊃id)
lem5-2 {A = t ‵= u} = ‵lam (‵join 0)

lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
lem5-3∋ zero    = zero
lem5-3∋ (suc i) = suc (lem5-3∋ i)

-- TODO: why does rewriting blow up constraint solver here?
module _ where
  lem5-3 : ∀ {Þ k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → Þ / Γ °§ ⊢ A °
  lem5-3 (‵var i)                = ‵var (lem5-3∋ i)
  lem5-3 (‵lam d)                = ‵lam (lem5-3 d)
  lem5-3 (d ‵$ e)                = lem5-3 d ‵$ lem5-3 e
  lem5-3 (‵pair d e)             = ‵pair (lem5-3 d) (lem5-3 e)
  lem5-3 (‵fst d)                = ‵fst (lem5-3 d)
  lem5-3 (‵snd d)                = ‵snd (lem5-3 d)
  lem5-3 (‵left d)               = ‵return (‵left (lem5-3 d))
  lem5-3 (‵right d)              = ‵return (‵right (lem5-3 d))
  lem5-3 (‵either c d e)         = lem5-2 ‵$ (lem5-3 c ‵>>= ‵lam (‵either 0
                                     (‵return (‵exch (wk (lem5-3 d))))
                                     (‵return (‵exch (wk (lem5-3 e))))))
  lem5-3 {Γ = Γ} (‵all refl d)
      = ‵all refl (TODO2 {Γ = Γ} (lem5-3 d))

  lem5-3 (‵unall t refl d)       = ‵unall t TODO1 (lem5-3 d)
  lem5-3 (‵ex t refl d)          = ‵return (‵ex t TODO1 (lem5-3 d))

  lem5-3 {Γ = Γ} (‵letex {C = C} refl refl d e)
      = lem5-2 ‵$
          (lem5-3 d ‵>>=
            ‵lam (‵letex refl refl 0
              (‵return (‵exch (wk (TODO5 {Γ = Γ} {C = C} (lem5-3 e)))))))

  lem5-3 (‵magicPA d)            = lem5-2 ‵$ ‵lam (lem5-3 d)
  lem5-3 ‵refl                   = ‵return ‵refl
  lem5-3 (‵sym d)                = lem5-3 d ‵>>= ‵lam
                                     (‵return (‵sym 0))
  lem5-3 (‵trans d e)            = lem5-3 d ‵>>= ‵lam
                                     (wk (lem5-3 e) ‵>>= ‵lam
                                       (‵return (‵trans 1 0)))
  lem5-3 (‵cong f i refl refl d) = lem5-3 d ‵>>= ‵lam
                                     (‵return (‵cong f i refl refl 0))
  lem5-3 ‵dis                    = ‵return ‵dis
  lem5-3 (‵inj d)                = lem5-3 d ‵>>= ‵lam
                                     (‵return (‵inj 0))
  lem5-3 (‵ind refl refl d e)    = ‵ind refl refl (TODO3 (lem5-3 d)) (TODO4 (lem5-3 e))
  lem5-3 (‵proj i refl)          = ‵return (‵proj i refl)
  lem5-3 (‵comp g φ refl)        = ‵return (‵comp g φ refl)
  lem5-3 (‵rec {t = t} f g)      = ‵pair
                                     (‵return (‵fst (‵rec {t = t} f g)))
                                     (‵return (‵snd (‵rec f g)))

-- "Note that the converse of 3 trivially holds wih 1."
lem5-3⁻¹ : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ °§ ⊢ A ° → PA / Γ ⊢ A
lem5-3⁻¹ d = aux (‵fst lem5-1 ‵$ lem2 d)
  where
    aux : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ °§ ⊢ A → PA / Γ ⊢ A
    aux {Γ = ∙}     d = d
    aux {Γ = Γ , C} d = wk (aux (‵lam d)) ‵$ (‵snd lem5-1 ‵$ 0)

-- TODO: "A counterexample for 4 is ¬∀y.A[y/x₀]."
-- lem5-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {A} → HA / Γ , ‵¬ (‵∀ A) ⊢ (‵¬ (‵∀ A)) °)
-- lem5-4 = {!!}


----------------------------------------------------------------------------------------------------

-- A-translation

_ᴬ⟨_⟩ : ∀ {k} → Fm k → Fm k → Fm k
(A ‵⊃ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
(A ‵∧ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
(A ‵∨ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
(‵∀ A)   ᴬ⟨ T ⟩ = ‵∀ A ᴬ⟨ wkFm T ⟩
(‵∃ A)   ᴬ⟨ T ⟩ = ‵∃ A ᴬ⟨ wkFm T ⟩
‵⊥      ᴬ⟨ T ⟩ = T
(t ‵= u) ᴬ⟨ T ⟩ = (t ‵= u) ‵∨ T

_ᴬ⟨_⟩§ : ∀ {k} → Fm§ k → Fm k → Fm§ k
∙       ᴬ⟨ T ⟩§ = ∙
(Γ , A) ᴬ⟨ T ⟩§ = Γ ᴬ⟨ T ⟩§ , A ᴬ⟨ T ⟩

-- TODO: interactions between A-translation and renaming/substitution
module _ where
  postulate
    TODO6 : ∀ {k} {A : Fm (suc k)} {T t} → (A ᴬ⟨ wkFm T ⟩) [ t /0]Fm ≡ (A [ t /0]Fm) ᴬ⟨ T ⟩
  -- TODO6 = ?

-- TODO: lemma 6
module _ where
  open ≡

  -- non-constructive lemma
  aux1 : ∀ {k} {Γ : Fm§ k} {A B C} → PA / Γ ⊢ (A ‵∨ C) ‵⊃ (B ‵∨ C) ‵⫗ (A ‵⊃ B) ‵∨ C
  aux1 = ‵pair
           (‵lam (‵either ‵em
             (‵right 0)
             (‵left (‵lam
               (‵either (2 ‵$ (‵left 0))
                 0
                 (‵abort (2 ‵$ 0)))))))
           (‵lam (‵lam (‵either 0
             (‵either 2
               (‵left (0 ‵$ 1))
               (‵right 0))
             (‵right 0))))

  aux2 : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵∨ C) ‵∧ (B ‵∨ C) ‵⫗ (A ‵∧ B) ‵∨ C
  aux2 = ‵pair
           (‵lam (‵either (‵fst 0)
             (‵either (‵snd 1)
               (‵left (‵pair 1 0))
               (‵right 0))
             (‵right 0)))
           (‵lam (‵either 0
             (‵pair (‵left (‵fst 0)) (‵left (‵snd 0)))
             (‵pair (‵right 0) (‵right 0))))

  aux3 : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵∨ C) ‵∨ (B ‵∨ C) ‵⫗ (A ‵∨ B) ‵∨ C
  aux3 = ‵pair
           (‵lam (‵either 0
             (‵either 0
               (‵left (‵left 0))
               (‵right 0))
             (‵either 0
               (‵left (‵right 0))
               (‵right 0))))
           (‵lam (‵either 0
             (‵either 0
               (‵left (‵left 0))
               (‵right (‵left 0)))
             (‵left (‵right 0)))) -- could also be ‵right

  -- non-constructive lemma
  aux4 : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ wkFm C) ‵⫗ ‵∀ A ‵∨ C
  aux4 {A = A} {C} = ‵pair
                       (‵lam (‵either ‵em
                         (‵right 0)
                         (‵left
                           (‵all refl (‵either (‵unall (‵tvar 0) (idcutFm (A ‵∨ wkFm C)) 1)
                             0
                             (‵abort (1 ‵$ 0)))))))
                       (‵lam (‵either 0
                         (‵all refl (‵left (‵unall (‵tvar 0) (idcutFm A) 0)))
                         (‵all refl (‵right 0))))

  aux5 : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ ‵∃ (A ‵∨ wkFm C) ‵⫗ ‵∃ A ‵∨ C
  aux5 {A = A} {C} = ‵pair
                       (‵lam (‵letex refl refl 0 (‵either 0
                         (‵left (‵ex (‵tvar 0) (idcutFm A) 0))
                         (‵right 0))))
                       (‵lam (‵either 0
                         (‵letex refl refl 0
                           (‵ex (‵tvar 0) (_‵∨_ & idcutFm A ⊗ idcutFm (wkFm C)) (‵left 0)))
                         (‵ex 𝟘 -- could also be any other natural
                           ( (subFm (idTm§ , 𝟘) A ‵∨_)
                               & ( eqsubFm idTm§ 𝟘 C
                                 ⋮ idsubFm C
                                 )
                           )
                           (‵right 0))))

  aux6 : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ C ‵⫗ ‵⊥ ‵∨ C
  aux6 = ‵pair
           (‵lam (‵right 0))
           (‵lam (‵either 0 (‵abort 0) 0))

module _ where
  open ⫗-Reasoning

  lem6-1 : ∀ {k} {Γ : Fm§ k} {A T} → PA / Γ ⊢ A ᴬ⟨ T ⟩ ‵⫗ A ‵∨ T
  lem6-1 {A = A ‵⊃ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
                            ⫗⟨ ‵cong⊃ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵⊃ (B ‵∨ T)
                            ⫗⟨ aux1 ⟩
                              (A ‵⊃ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∧ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
                            ⫗⟨ ‵cong∧ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∧ (B ‵∨ T)
                            ⫗⟨ aux2 ⟩
                              (A ‵∧ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∨ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
                            ⫗⟨ ‵cong∨ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∨ (B ‵∨ T)
                            ⫗⟨ aux3 ⟩
                              (A ‵∨ B) ‵∨ T
                            ∎
  lem6-1 {A = ‵∀ A}   {T} = begin
                              ‵∀ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ ‵cong∀ lem6-1 ⟩
                              ‵∀ (A ‵∨ wkFm T)
                            ⫗⟨ aux4 ⟩
                              ‵∀ A ‵∨ T
                            ∎
  lem6-1 {A = ‵∃ A}   {T} = begin
                              ‵∃ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ ‵cong∃ lem6-1 ⟩
                              ‵∃ (A ‵∨ wkFm T)
                            ⫗⟨ aux5 ⟩
                              ‵∃ A ‵∨ T
                            ∎
  lem6-1 {A = ‵⊥}    {T} = aux6
  lem6-1 {A = t ‵= u} {T} = ⫗refl

-- lem6-2 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ T ‵⊃ A ᴬ⟨ T ⟩
-- lem6-2 {A = A ‵⊃ B}    = ‵lam (‵lam (lem6-2 ‵$ 1)) -- function argument ignored
-- lem6-2 {A = A ‵∧ B}    = ‵lam (‵pair (lem6-2 ‵$ 0) (lem6-2 ‵$ 0))
-- lem6-2 {A = A ‵∨ B}    = ‵lam (‵left (lem6-2 ‵$ 0)) -- could also be ‵right
-- lem6-2 {A = ‵∀ A}      = ‵lam (‵all refl (lem6-2 ‵$ 0))
-- lem6-2 {A = ‵∃ A}  {T} = {!!}
-- -- ‵lam (‵ex 𝟘 (TODO6 {A = A} {T}) (lem6-2 {A = A [ 𝟘 /0]Fm} ‵$ 0)) -- TODO: termination failure
-- lem6-2 {A = ‵⊥}       = ⊃id
-- lem6-2 {A = t ‵= u}    = ‵lam (‵right 0)
--
-- lem6-3∋ : ∀ {k} {Γ : Fm§ k} {A T} → Γ ∋ A → Γ ᴬ⟨ T ⟩§ ∋ A ᴬ⟨ T ⟩
-- lem6-3∋ zero    = zero
-- lem6-3∋ (suc i) = suc (lem6-3∋ i)

-- TODO: "The proof of 3 is a bit tricky where eigenvariable conditions are involved."
-- lem6-3 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ A → Þ / Γ ᴬ⟨ T ⟩§ ⊢ A ᴬ⟨ T ⟩
-- lem6-3 (‵var i)                = ‵var (lem6-3∋ i)
-- lem6-3 (‵lam d)                = ‵lam (lem6-3 d)
-- lem6-3 (d ‵$ e)                = lem6-3 d ‵$ lem6-3 e
-- lem6-3 (‵pair d e)             = ‵pair (lem6-3 d) (lem6-3 e)
-- lem6-3 (‵fst d)                = ‵fst (lem6-3 d)
-- lem6-3 (‵snd d)                = ‵snd (lem6-3 d)
-- lem6-3 (‵left d)               = ‵left (lem6-3 d)
-- lem6-3 (‵right d)              = ‵right (lem6-3 d)
-- lem6-3 (‵either c d e)         = ‵either (lem6-3 c) (lem6-3 d) (lem6-3 e)
-- lem6-3 (‵all refl d)           = {!!}
-- lem6-3 (‵unall t refl d)       = {!!}
-- lem6-3 (‵ex t refl d)          = {!!}
-- lem6-3 (‵letex refl refl d e)  = {!!}
-- lem6-3 (‵abort d)              = {!!}
-- lem6-3 (‵magic d)              = {!!}
-- lem6-3 ‵refl                   = ‵left ‵refl
-- lem6-3 (‵sym d)                = ‵either (lem6-3 d)
--                                    (‵left (‵sym 0))
--                                    (‵right 0)
-- lem6-3 (‵trans d e)            = ‵either (lem6-3 d)
--                                    (‵either (wk (lem6-3 e))
--                                      (‵left (‵trans 1 0))
--                                      (‵right 0))
--                                    (‵right 0)
-- lem6-3 (‵cong f i refl refl d) = {!!}
-- lem6-3 ‵dis                    = {!!}
-- lem6-3 (‵inj d)                = {!!}
-- lem6-3 (‵ind refl refl d e)    = {!!}
-- lem6-3 (‵proj i refl)          = {!!}
-- lem6-3 (‵comp g φ refl)        = {!!}
-- lem6-3 (‵rec f g)              = {!!}

-- TODO: "A counterexample for 4 is A = ¬¬T."
-- lem6-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {T} → HA / Γ , ‵¬ ‵¬ T ⊢ (‵¬ ‵¬ T) ᴬ⟨ T ⟩)
-- lem6-4 = {!!}


----------------------------------------------------------------------------------------------------

-- proof of theorem 1

-- TODO: lemma 7
-- TODO: corollary 8
-- TODO: theorem 1


----------------------------------------------------------------------------------------------------
```

Lorem ipsum dolor sit amet, consectetur adipisicing elit, sed do eiusmod tempor incididunt ut labore
et dolore magna aliqua.  Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut
aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse
cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in
culpa qui officia deserunt mollit anim id est laborum.
