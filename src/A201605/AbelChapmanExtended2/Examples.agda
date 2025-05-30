{-# OPTIONS --sized-types #-}

module A201605.AbelChapmanExtended2.Examples where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import A201605.AbelChapmanExtended2.Syntax
open import A201605.AbelChapmanExtended2.Termination




I : ∀ {Γ a} → Tm Γ (a ⇒ a)
I = lam v₀

K : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ a)
K = lam (lam v₁)

S : ∀ {Γ a b c} → Tm Γ ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
S = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))


II : ∀ {Γ a} → Tm Γ (a ⇒ a)
II = app I I

II≡I : nf (II {∅} {⊥}) ≡ nf I
II≡I = refl


SKK : ∀ {Γ a} → Tm Γ (a ⇒ a)
SKK {a = a} = app (app S K) (K {b = a ⇒ a})

SKK≡I : nf (SKK {∅} {⊥}) ≡ nf I
SKK≡I = refl


SKSK : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ a)
SKSK = app (app (app S K) S) K

SKSK≡K : nf (SKSK {∅} {⊥} {⊥ ⇒ ⊥}) ≡ nf K
SKSK≡K = refl


flip : ∀ {Γ a b c} → Tm Γ ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
flip = lam (lam (lam (app (app v₂ v₀) v₁)))

flip-flip-K≡K : nf (app flip (app flip (K {∅} {⊥} {⊥ ⇒ ⊥}))) ≡ nf K
flip-flip-K≡K = refl


fst′ : ∀ {Γ a b} → Tm Γ (a ∧ b ⇒ a)
fst′ = lam (fst v₀)

snd′ : ∀ {Γ a b} → Tm Γ (a ∧ b ⇒ b)
snd′ = lam (snd v₀)

pair′ : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ a ∧ b)
pair′ = lam (lam (pair v₁ v₀))

fst-pair : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ a)
fst-pair = lam (lam (app fst′ (app (app pair′ v₁) v₀)))

snd-pair : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ b)
snd-pair = lam (lam (app snd′ (app (app pair′ v₁) v₀)))

fst-pair≡K : nf (fst-pair {∅} {⊥} {⊥ ⇒ ⊥}) ≡ nf K
fst-pair≡K = refl

snd-pair≡flip-K : nf (snd-pair {∅} {⊥} {⊥ ⇒ ⊥}) ≡ nf (app flip K)
snd-pair≡flip-K = refl


contradiction : ∀ {Γ a b} → Tm Γ (a ⇒ ¬ a ⇒ b)
contradiction = lam (lam (boom (app v₀ v₁)))

contraposition : ∀ {Γ a b} → Tm Γ ((a ⇒ b) ⇒ ¬ b ⇒ ¬ a)
contraposition = lam (lam (lam (app (app contradiction (app v₂ v₀)) v₁)))

¬-flip : ∀ {Γ a b} → Tm Γ ((a ⇒ ¬ b) ⇒ b ⇒ ¬ a)
¬-flip = flip

¬¬-map : ∀ {Γ a b} → Tm Γ ((a ⇒ b) ⇒ ¬ ¬ a ⇒ ¬ ¬ b)
¬¬-map = lam (app contraposition (app contraposition v₀))


inl′ : ∀ {Γ a b} → Tm Γ (a ⇒ a ∨ b)
inl′ = lam (inl v₀)

inr′ : ∀ {Γ a b} → Tm Γ (b ⇒ a ∨ b)
inr′ = lam (inr v₀)

case′ : ∀ {Γ a b c} → Tm Γ (a ∨ b ⇒ (a ⇒ c) ⇒ (b ⇒ c) ⇒ c)
case′ = lam (lam (lam (case v₂ (app v₂ v₀) (app v₁ v₀))))

case-inl : ∀ {Γ a b c} → Tm Γ (a ⇒ (a ⇒ c) ⇒ (b ⇒ c) ⇒ c)
case-inl = lam (lam (lam (app (app (app case′ (app inl′ v₂)) v₁) v₀)))

case-inr : ∀ {Γ a b c} → Tm Γ (b ⇒ (a ⇒ c) ⇒ (b ⇒ c) ⇒ c)
case-inr = lam (lam (lam (app (app (app case′ (app inr′ v₂)) v₁) v₀)))


dm1 : ∀ {Γ a b} → Tm Γ (¬ a ∧ ¬ b ⇔ ¬ (a ∨ b))
dm1 = pair (lam (lam (case v₀ (app (fst v₂) v₀) (app (snd v₂) v₀))))
           (lam (pair (lam (app v₁ (inl v₀))) (lam (app v₁ (inr v₀)))))

dm2 : ∀ {Γ a b} → Tm Γ (¬ a ∨ ¬ b ⇒ ¬ (a ∧ b))
dm2 = lam (lam (case v₁ (app v₀ (fst v₁)) (app v₀ (snd v₁))))

testl : ∀ {Γ a b} → Tm Γ (¬ a ⇒ ¬ b ⇒ ¬ a ∧ ¬ b)
testl = lam (lam (app (snd dm1) (app (fst dm1) (pair v₁ v₀))))

testr : ∀ {Γ a b} → Tm Γ (¬ a ⇒ ¬ b ⇒ ¬ a ∧ ¬ b)
testr = lam (lam (pair v₁ v₀))

test : nf (testl {∅} {⊥} {⊥ ⇒ ⊥}) ≡ nf testr
test = refl
