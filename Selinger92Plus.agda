module Selinger92Plus where

open import Axiom.UniquenessOfIdentityProofs.WithK public
  using (uip)

open import Selinger92


----------------------------------------------------------------------------------------------------

-- TODO: prove these without K?

-- uipNat : ∀ {n ^n : Nat} (p ^p : ^n ≡ n) → ^p ≡ p
-- uipNat refl refl = refl
--
-- uipList : ∀ {𝓍} {X : Set 𝓍} {ξ ^ξ : List X} (p ^p : ^ξ ≡ ξ) → ^p ≡ p
-- uipList refl refl = refl
--
-- uipVec : ∀ {𝓍} {X : Set 𝓍} {n} {ξ ^ξ : Vec X n} (p ^p : ^ξ ≡ ξ) → ^p ≡ p
-- uipVec refl refl = refl
--
-- uipPrim : ∀ {n} {f ^f : Prim n} (p ^p : ^f ≡ f) → ^p ≡ p
-- uipPrim refl refl = refl
--
-- uipFin : ∀ {k} {i ^i : Fin k} (p ^p : ^i ≡ i) → ^p ≡ p
-- uipFin refl refl = refl
--
-- uip≤ : ∀ {k k′} {η ^η : k ≤ k′} (p ^p : ^η ≡ η) → ^p ≡ p
-- uip≤ refl refl = refl
--
-- uip∋ : ∀ {𝓍} {X : Set 𝓍} {Γ : List X} {A} {i ^i : Γ ∋ A} (p ^p : ^i ≡ i) → ^p ≡ p
-- uip∋ refl refl = refl
--
-- uip⊑ : ∀ {𝓍} {X : Set 𝓍} {Γ Γ′ : List X} {η ^η : Γ ⊑ Γ′} (p ^p : ^η ≡ η) → ^p ≡ p
-- uip⊑ refl refl = refl
--
-- uipTm : ∀ {k} {t ^t : Tm k} (p ^p : ^t ≡ t) → ^p ≡ p
-- uipTm refl refl = refl
--
-- uipTm§ : ∀ {k n} {τ ^τ : Tm§ k n} (p ^p : ^τ ≡ τ) → ^p ≡ p
-- uipTm§ refl refl = refl
--
-- uipFm : ∀ {k} {A ^A : Fm k} (p ^p : ^A ≡ A) → ^p ≡ p
-- uipFm refl refl = refl
--
-- uipFm§ : ∀ {k} {Γ ^Γ : Fm§ k} (p ^p : ^Γ ≡ Γ) → ^p ≡ p
-- uipFm§ refl refl = refl
--
-- uip : ∀ {Þ k} {Γ : Fm§ k} {A} {d ^d : Þ / Γ ⊢ A} (p ^p : ^d ≡ d) → ^p ≡ p
-- uip refl refl = refl
--
-- uip§ : ∀ {Þ k} {Γ Δ : Fm§ k} {δ ^δ : Þ / Γ ⊢§ Δ} (p ^p : ^δ ≡ δ) → ^p ≡ p
-- uip§ refl refl = refl


----------------------------------------------------------------------------------------------------

bicast⊑ : ∀ {k} {Γ ^Γ Γ′ ^Γ′ : Fm§ k} → ^Γ ≡ Γ → ^Γ′ ≡ Γ′ → Γ ⊑ Γ′ → ^Γ ⊑ ^Γ′
bicast⊑ refl refl η = η

wkbicast⊑ : ∀ {k} {Γ ^Γ Γ′ ^Γ′ : Fm§ k} {C ^C} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ′ ≡ Γ′) (q : ^C ≡ C)
              (η : Γ ⊑ Γ′) →
              wk⊑ (bicast⊑ p₁ p₂ η) ≡ bicast⊑ p₁ (_,_ & p₂ ⊗ q) (wk⊑ η)
wkbicast⊑ refl refl refl η = refl

liftbicast⊑ : ∀ {k} {Γ ^Γ Γ′ ^Γ′ : Fm§ k} {C ^C} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ′ ≡ Γ′) (q : ^C ≡ C)
                (η : Γ ⊑ Γ′) →
                lift⊑ (bicast⊑ p₁ p₂ η) ≡ bicast⊑ (_,_ & p₁ ⊗ q) (_,_ & p₂ ⊗ q) (lift⊑ η)
liftbicast⊑ refl refl refl η = refl

lidtren⊑ : ∀ {k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) →
             tren⊑ id≤ η ≡ bicast⊑ (lidrenFm§ Γ) (lidrenFm§ Γ′) η
lidtren⊑ stop      = refl
lidtren⊑ (wk⊑ η)   = wk⊑ & lidtren⊑ η
                   ⋮ wkbicast⊑ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) η
lidtren⊑ (lift⊑ η) = lift⊑ & lidtren⊑ η
                   ⋮ liftbicast⊑ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) η

lcomptren⊑ : ∀ {k k′ k″} {Γ Γ′ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊑ Γ′) →
               tren⊑ (η′ ∘≤ η) ζ ≡
                 bicast⊑ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) (tren⊑ η′ (tren⊑ η ζ))
lcomptren⊑ η′ η stop      = refl
lcomptren⊑ η′ η (wk⊑ ζ)   = wk⊑ & lcomptren⊑ η′ η ζ
                          ⋮ wkbicast⊑ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
                              (tren⊑ η′ (tren⊑ η ζ))
lcomptren⊑ η′ η (lift⊑ ζ) = lift⊑ & lcomptren⊑ η′ η ζ
                          ⋮ liftbicast⊑ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
                              (tren⊑ η′ (tren⊑ η ζ))


----------------------------------------------------------------------------------------------------

bicast∋ : ∀ {k} {Γ ^Γ : Fm§ k} {A ^A} → ^Γ ≡ Γ → ^A ≡ A → Γ ∋ A → ^Γ ∋ ^A
bicast∋ refl refl i = i

zerobicast∋ : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (p : ^Γ ≡ Γ) (q : ^C ≡ C) →
                zero ≡ bicast∋ (_,_ & p ⊗ q) q zero
zerobicast∋ refl refl = refl

sucbicast∋ : ∀ {k} {Γ ^Γ : Fm§ k} {A ^A C ^C} (p : ^Γ ≡ Γ) (q₁ : ^C ≡ C) (q₂ : ^A ≡ A)
               (i : Γ ∋ A) →
               suc (bicast∋ p q₂ i) ≡ bicast∋ (_,_ & p ⊗ q₁) q₂ (suc i)
sucbicast∋ refl refl refl zero    = refl
sucbicast∋ refl refl refl (suc i) = suc & sucbicast∋ refl refl refl i

lidtren∋ : ∀ {k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → tren∋ id≤ i ≡ bicast∋ (lidrenFm§ Γ) (lidrenFm A) i
lidtren∋ zero    = zerobicast∋ (lidrenFm§ _) (lidrenFm _)
lidtren∋ (suc i) = suc & lidtren∋ i
                 ⋮ sucbicast∋ (lidrenFm§ _) (lidrenFm _) (lidrenFm _) i

comptren∋ : ∀ {k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
              tren∋ (η′ ∘≤ η) i ≡
                bicast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) (tren∋ η′ (tren∋ η i))
comptren∋ η′ η zero    = zerobicast∋ (comprenFm§ η′ η _) (comprenFm η′ η _)
comptren∋ η′ η (suc i) = suc & comptren∋ η′ η i
                       ⋮ sucbicast∋ (comprenFm§ η′ η _) (comprenFm η′ η _) (comprenFm η′ η _)
                           (tren∋ η′ (tren∋ η i))


----------------------------------------------------------------------------------------------------

bicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A} → ^Γ ≡ Γ → ^A ≡ A → Þ / Γ ⊢ A → Þ / ^Γ ⊢ ^A
bicast refl refl d = d

varbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A} (p : ^Γ ≡ Γ) (q : ^A ≡ A) (i : Γ ∋ A) →
            ‵var {Þ = Þ} (bicast∋ p q i) ≡ bicast p q (‵var i)
varbicast refl refl i = refl

lambicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
              (d : Þ / Γ , A ⊢ B) →
              ‵lam (bicast (_,_ & p ⊗ q₁) q₂ d) ≡ bicast p (_‵⊃_ & q₁ ⊗ q₂) (‵lam d)
lambicast refl refl refl d = refl

appbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
              (d : Þ / Γ ⊢ A ‵⊃ B) (e : Þ / Γ ⊢ A) →
              (bicast p (_‵⊃_ & q₁ ⊗ q₂) d ‵$ bicast p q₁ e) ≡ bicast p q₂ (d ‵$ e)
appbicast refl refl refl d e = refl

pairbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
               (d : Þ / Γ ⊢ A) (e : Þ / Γ ⊢ B) →
               ‵pair (bicast p q₁ d) (bicast p q₂ e) ≡ bicast p (_‵∧_ & q₁ ⊗ q₂) (‵pair d e)
pairbicast refl refl refl d e = refl

fstbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
              (d : Þ / Γ ⊢ A ‵∧ B) →
              ‵fst (bicast p (_‵∧_ & q₁ ⊗ q₂) d) ≡ bicast p q₁ (‵fst d)
fstbicast refl refl refl d = refl

sndbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
              (d : Þ / Γ ⊢ A ‵∧ B) →
              ‵snd (bicast p (_‵∧_ & q₁ ⊗ q₂) d) ≡ bicast p q₂ (‵snd d)
sndbicast refl refl refl d = refl

leftbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
               (d : Þ / Γ ⊢ A) →
               ‵left (bicast p q₁ d) ≡ bicast p (_‵∨_ & q₁ ⊗ q₂) (‵left d)
leftbicast refl refl refl d = refl

rightbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
                (d : Þ / Γ ⊢ B) →
                ‵right (bicast p q₂ d) ≡ bicast p (_‵∨_ & q₁ ⊗ q₂) (‵right d)
rightbicast refl refl refl d = refl

eitherbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B C ^C} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
                 (q₃ : ^C ≡ C) (c : Þ / Γ ⊢ A ‵∨ B) (d : Þ / Γ , A ⊢ C) (e : Þ / Γ , B ⊢ C) →
                 ‵either (bicast p (_‵∨_ & q₁ ⊗ q₂) c) (bicast (_,_ & p ⊗ q₁) q₃ d)
                     (bicast (_,_ & p ⊗ q₂) q₃ e) ≡
                   bicast p q₃ (‵either c d e)
eitherbicast refl refl refl refl c d e = refl

-- allbicast
-- unallbicast
-- exbicast
-- letexbicast

abortbicast : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (p : ^Γ ≡ Γ) (q : ^C ≡ C) (d : HA / Γ ⊢ ‵⊥) →
                ‵abort (bicast p refl d) ≡ bicast p q (‵abort d)
abortbicast refl refl d = refl

magicbicast : ∀ {k} {Γ ^Γ : Fm§ k} {A ^A} (p : ^Γ ≡ Γ) (q : ^A ≡ A) (d : PA / Γ , ‵¬ A ⊢ ‵⊥) →
                ‵magic (bicast (_,_ & p ⊗ (_‵⊃_ & q ⊗ refl)) refl d) ≡ bicast p q (‵magic d)
magicbicast refl refl d = refl

reflbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t} (p : ^Γ ≡ Γ) (q : ^t ≡ t) →
               ‵refl {Þ = Þ} ≡ bicast p (_‵=_ & q ⊗ q) ‵refl
reflbicast refl refl = refl

symbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^t ≡ t) (q₂ : ^u ≡ u)
              (d : Þ / Γ ⊢ t ‵= u) →
              ‵sym (bicast p (_‵=_ & q₁ ⊗ q₂) d) ≡ bicast p (_‵=_ & q₂ ⊗ q₁) (‵sym d)
symbicast refl refl refl d = refl

transbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {s ^s t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^s ≡ s) (q₂ : ^t ≡ t)
                (q₃ : ^u ≡ u) (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) →
                ‵trans (bicast p (_‵=_ & q₁ ⊗ q₂) d) (bicast p (_‵=_ & q₂ ⊗ q₃) e) ≡
                  bicast p (_‵=_ & q₁ ⊗ q₃) (‵trans d e)
transbicast refl refl refl refl d e = refl

-- congbicast

disbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t} (p : ^Γ ≡ Γ) (q : ^t ≡ t) →
              ‵dis {Þ = Þ} {t = ^t} ≡
                bicast p
                  (_‵⊃_
                    & (_‵=_ & (‵fun suc & (refl ⊗ q)) ⊗ refl)
                    ⊗ refl) (‵dis {t = t})
disbicast refl refl = refl

injbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^t ≡ t) (q₂ : ^u ≡ u)
                (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) →
              ‵inj (bicast p
                  (_‵=_
                    & (‵fun suc & (refl ⊗ q₁))
                    ⊗ ‵fun suc & (refl ⊗ q₂)) d) ≡
                bicast p (_‵=_ & q₁ ⊗ q₂) (‵inj d)
injbicast refl refl refl d = refl

-- indbicast
-- projbicast
-- compbicast

recbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n ^τ τ t ^t f g} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (q : ^t ≡ t) →
              ‵rec {Þ = Þ} {n = n} f g ≡
                bicast p₁
                  (_‵∧_
                    & (_‵=_
                        & (‵fun (rec f g) & (_,_ & p₂ ⊗ refl))
                        ⊗ ‵fun f & p₂)
                    ⊗ (_‵=_
                        & (‵fun (rec f g) & (_,_ & p₂ ⊗ ‵fun suc & (_⊗_ {f = (∙ ,_)} refl q)))
                        ⊗ ‵fun g
                            & (_,_
                                & (_,_ & p₂ ⊗ q)
                                ⊗ ‵fun (rec f g) & (_,_ & p₂ ⊗ q))))
                  (‵rec f g)
recbicast refl refl refl = refl

module _ where
  open ≡-Reasoning

  matchpeek : ∀ {k n} {τ ^τ : Tm§ k n} {t ^t} (p : ^τ ≡ τ) (q : ^t ≡ t) (i : Fin n)
               (r : peek i τ ≡ t) →
               peek i ^τ ≡ ^t
  matchpeek refl refl i r = r

  projbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n} {τ ^τ t ^t} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (q : ^t ≡ t)
                 (i : Fin n) (r : peek i τ ≡ t) →
                 ‵proj i (matchpeek p₂ q i r) ≡
                   bicast {Þ = Þ} p₁
                     (_‵=_
                       & (‵fun (proj i) & p₂)
                       ⊗ q)
                     (‵proj i r)
  projbicast refl refl refl i r = refl

  matchfor : ∀ {k n m τ ^τ τ∗ ^τ∗} (p₁ : ^τ ≡ τ) (p₂ : ^τ∗ ≡ τ∗) (φ : Prim§ n m)
               (r : for φ (flip (‵fun {k = k}) τ) ≡ τ∗) →
               for φ (flip ‵fun ^τ) ≡ ^τ∗
  matchfor refl refl φ r = r

  compbicast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n m τ ^τ τ∗ ^τ∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (p₃ : ^τ∗ ≡ τ∗)
                 (g : Prim m) (φ : Prim§ n m) (r : for φ (flip ‵fun τ) ≡ τ∗) →
                 ‵comp {Þ = Þ} g φ (matchfor p₂ p₃ φ r) ≡
                   bicast p₁
                     (_‵=_
                       & (‵fun (comp g φ) & p₂)
                       ⊗ ‵fun g & p₃)
                     (‵comp g φ r)
  compbicast refl refl refl g φ r = refl

  lidtren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) →
              tren id≤ d ≡ bicast (lidrenFm§ Γ) (lidrenFm A) d
  lidtren (‵var i)                = ‵var & lidtren∋ i
                                  ⋮ varbicast (lidrenFm§ _) (lidrenFm _) i
  lidtren (‵lam d)                = ‵lam & lidtren d
                                  ⋮ lambicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
  lidtren (d ‵$ e)                = _‵$_ & lidtren d ⊗ lidtren e
                                  ⋮ appbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d e
  lidtren (‵pair d e)             = ‵pair & lidtren d ⊗ lidtren e
                                  ⋮ pairbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d e
  lidtren (‵fst d)                = ‵fst & lidtren d
                                  ⋮ fstbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
  lidtren (‵snd d)                = ‵snd & lidtren d
                                  ⋮ sndbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
  lidtren (‵left d)               = ‵left & lidtren d
                                  ⋮ leftbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
  lidtren (‵right d)              = ‵right & lidtren d
                                  ⋮ rightbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
  lidtren (‵either c d e)         = ‵either & lidtren c ⊗ lidtren d ⊗ lidtren e
                                  ⋮ eitherbicast (lidrenFm§ _) (lidrenFm _) (lidrenFm _)
                                      (lidrenFm _) c d e
  lidtren {Γ = Γ} (‵all {A = A} refl d) = {!!}
  lidtren (‵unall t refl d)       = {!!}
  lidtren (‵ex t refl d)          = {!!}
  lidtren (‵letex refl refl d e)  = {!!}
  lidtren (‵abort d)              = ‵abort & lidtren d
                                  ⋮ abortbicast (lidrenFm§ _) (lidrenFm _) d
  lidtren (‵magic d)              = ‵magic & lidtren d
                                  ⋮ magicbicast (lidrenFm§ _) (lidrenFm _) d
  lidtren ‵refl                   = reflbicast (lidrenFm§ _) (lidrenTm _)
  lidtren (‵sym d)                = ‵sym & lidtren d
                                  ⋮ symbicast (lidrenFm§ _) (lidrenTm _) (lidrenTm _) d
  lidtren (‵trans d e)            = ‵trans & lidtren d ⊗ lidtren e
                                  ⋮ transbicast (lidrenFm§ _) (lidrenTm _) (lidrenTm _)
                                      (lidrenTm _) d e
  lidtren (‵cong f i refl refl d) = {!!}
  lidtren ‵dis                    = disbicast (lidrenFm§ _) (lidrenTm _)
  lidtren (‵inj d)                = ‵inj & lidtren d
                                  ⋮ injbicast (lidrenFm§ _) (lidrenTm _) (lidrenTm _) d
  lidtren (‵ind refl refl d e)    = {!!}
  lidtren {Γ = Γ} (‵proj {τ = τ} {t} i p) =
      begin
        ‵proj i (eqrenpeekTm id≤ i τ ⋮ renTm id≤ & p)
      ≡⟨ ‵proj i
           & uip (eqrenpeekTm id≤ i τ ⋮ renTm id≤ & p) (matchpeek (lidrenTm§ τ) (lidrenTm t) i p) ⟩
        ‵proj i (matchpeek (lidrenTm§ τ) (lidrenTm t) i p)
      ≡⟨ projbicast (lidrenFm§ Γ) (lidrenTm§ τ) (lidrenTm t) i p ⟩
        bicast (lidrenFm§ Γ) (_‵=_ & (‵fun (proj i) & lidrenTm§ τ) ⊗ lidrenTm t) (‵proj i p)
      ∎
  lidtren {Γ = Γ} (‵comp {τ = τ} {τ∗} g φ p) =
      begin
        ‵comp g φ (eqrenforTm id≤ φ τ ⋮ renTm§ id≤ & p)
      ≡⟨ ‵comp g φ
          & uip (eqrenforTm id≤ φ τ ⋮ renTm§ id≤ & p) (matchfor (lidrenTm§ τ) (lidrenTm§ τ∗) φ p) ⟩
        ‵comp g φ (matchfor (lidrenTm§ τ) (lidrenTm§ τ∗) φ p)
      ≡⟨ compbicast (lidrenFm§ Γ) (lidrenTm§ τ) (lidrenTm§ τ∗) g φ p ⟩
        bicast (lidrenFm§ Γ) (_‵=_ & (‵fun (comp g φ) & lidrenTm§ τ) ⊗ ‵fun g & lidrenTm§ τ∗)
          (‵comp g φ p)
      ∎
  lidtren (‵rec f g)              = recbicast (lidrenFm§ _) (lidrenTm§ _) (lidrenTm _)

--   comptren : ∀ {Þ k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
--                tren (η′ ∘≤ η) d ≡
--                  bicast (comprenFm§ η′ η Γ) (comprenFm η′ η A) (tren η′ (tren η d))
--   comptren η′ η (‵var i)                = ‵var & comptren∋ η′ η i
--                                         ⋮ varbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (tren∋ η′ (tren∋ η i))
--   comptren η′ η (‵lam d)                = ‵lam & comptren η′ η d
--                                         ⋮ lambicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (d ‵$ e)                = _‵$_ & comptren η′ η d ⊗ comptren η′ η e
--                                         ⋮ appbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--                                             (tren η′ (tren η e))
--   comptren η′ η (‵pair d e)             = ‵pair & comptren η′ η d ⊗ comptren η′ η e
--                                         ⋮ pairbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--                                             (tren η′ (tren η e))
--   comptren η′ η (‵fst d)                = ‵fst & comptren η′ η d
--                                         ⋮ fstbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵snd d)                = ‵snd & comptren η′ η d
--                                         ⋮ sndbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵left d)               = ‵left & comptren η′ η d
--                                         ⋮ leftbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵right d)              = ‵right & comptren η′ η d
--                                         ⋮ rightbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵either c d e)         = ‵either
--                                             & comptren η′ η c
--                                             ⊗ comptren η′ η d
--                                             ⊗ comptren η′ η e
--                                         ⋮ eitherbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (comprenFm η′ η _) (comprenFm η′ η _)
--                                             (tren η′ (tren η c)) (tren η′ (tren η d))
--                                             (tren η′ (tren η e))
--   comptren η′ η (‵all refl d)           = {!!}
--   comptren η′ η (‵unall t refl d)       = {!!}
--   comptren η′ η (‵ex t refl d)          = {!!}
--   comptren η′ η (‵letex refl refl d e)  = {!!}
--   comptren η′ η (‵abort d)              = ‵abort & comptren η′ η d
--                                         ⋮ abortbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (tren η′ (tren η d))
--   comptren η′ η (‵magic d)              = ‵magic & comptren η′ η d
--                                         ⋮ magicbicast (comprenFm§ η′ η _) (comprenFm η′ η _)
--                                             (tren η′ (tren η d))
--   comptren η′ η ‵refl                   = reflbicast (comprenFm§ η′ η _) (comprenTm η′ η _)
--   comptren η′ η (‵sym d)                = ‵sym & comptren η′ η d
--                                         ⋮ symbicast (comprenFm§ η′ η _) (comprenTm η′ η _)
--                                             (comprenTm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵trans d e)            = ‵trans & comptren η′ η d ⊗ comptren η′ η e
--                                         ⋮ transbicast (comprenFm§ η′ η _) (comprenTm η′ η _)
--                                             (comprenTm η′ η _) (comprenTm η′ η _)
--                                             (tren η′ (tren η d)) (tren η′ (tren η e))
--   comptren η′ η (‵cong f i refl refl d) = {!!}
--   comptren η′ η ‵dis                    = disbicast (comprenFm§ η′ η _) (comprenTm η′ η _)
--   comptren η′ η (‵inj d)                = ‵inj & comptren η′ η d
--                                         ⋮ injbicast (comprenFm§ η′ η _) (comprenTm η′ η _)
--                                             (comprenTm η′ η _) (tren η′ (tren η d))
--   comptren η′ η (‵ind refl refl d e)    = {!!}
--   comptren η′ η (‵proj i refl)          = {!!}
--   comptren η′ η (‵comp g φ refl)        = {!!}
--   comptren η′ η (‵rec f g)              = recbicast (comprenFm§ η′ η _) (comprenTm§ η′ η _)
--                                             (comprenTm η′ η _)


-- ----------------------------------------------------------------------------------------------------

-- bicast§ : ∀ {Þ k} {Γ ^Γ : Fm§ k} {Δ ^Δ} → ^Γ ≡ Γ → ^Δ ≡ Δ → Þ / Γ ⊢§ Δ → Þ / ^Γ ⊢§ ^Δ
-- bicast§ refl refl δ = δ

-- nilbicast§ : ∀ {Þ k} {Γ ^Γ : Fm§ k} (p : ^Γ ≡ Γ) → ∙ ≡ bicast§ {Þ = Þ} p refl ∙
-- nilbicast§ refl = refl

-- consbicast§ : ∀ {Þ k} {Γ ^Γ Δ ^Δ : Fm§ k} {A ^A} (p₁ : ^Γ ≡ Γ) (p₂ : ^Δ ≡ Δ) (q : ^A ≡ A)
--                 (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) →
--                 (bicast§ p₁ p₂ δ , bicast p₁ q d) ≡ bicast§ p₁ (_,_ & p₂ ⊗ q) (δ , d)
-- consbicast§ refl refl refl δ d = refl

-- comptren§ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
--               tren§ (η′ ∘≤ η) δ ≡
--                 bicast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ))
-- comptren§ η′ η ∙       = nilbicast§ (comprenFm§ η′ η _)
-- comptren§ η′ η (δ , d) = _,_ & comptren§ η′ η δ ⊗ comptren η′ η d
--                        ⋮ consbicast§ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
--                            (tren§ η′ (tren§ η δ)) (tren η′ (tren η d))


-- ----------------------------------------------------------------------------------------------------

-- bicast§→≅ : ∀ {Þ k} {Γ ^Γ Δ ^Δ : Fm§ k} (p₁ : ^Γ ≡ Γ) (p₂ : ^Δ ≡ Δ) (δ : Þ / Γ ⊢§ Δ) →
--               bicast§ p₁ p₂ δ ≅ δ
-- bicast§→≅ refl refl δ = refl

-- -- TODO: maybe all uses of heteq in main file can be replaced with bicast/bicast§
-- hcomptren§′ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
--                 tren§ (η′ ∘≤ η) δ ≅ tren§ η′ (tren§ η δ)
-- hcomptren§′ {Γ = Γ} {Δ} η′ η δ =
--     begin
--       tren§ (η′ ∘≤ η) δ
--     ≡⟨ comptren§ η′ η δ ⟩
--       bicast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ))
--     ≅⟨ bicast§→≅ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ)) ⟩
--       tren§ η′ (tren§ η δ)
--     ∎
--   where
--     open ≅-Reasoning


-- ----------------------------------------------------------------------------------------------------
