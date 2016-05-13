module AbelChapmanExtended.Examples where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AbelChapmanExtended.Syntax
open import AbelChapmanExtended.Termination




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
