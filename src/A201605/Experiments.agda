{-# OPTIONS --sized-types #-}

module A201605.Experiments where

open import Data.Product using () renaming (_,_ to ⟨_,_⟩ ; proj₁ to π₁ ; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import A201605.AbelChapman


get : ∀ {Γ a} (t : Tm Γ a) → Nf Γ a
get {Γ} {a} t = π₁ (normalize Γ a t)


I : ∀ {a} → Tm ε (a ⇒ a)
I = lam (var top)

K : ∀ {a b} → Tm ε (a ⇒ b ⇒ a)
K = lam (lam (var (pop top)))

S : ∀ {a b c} → Tm ε ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
S = lam (lam (lam (app (app (var (pop (pop top))) (var top)) (app (var (pop top)) (var top)))))


II : ∀ {a} → Tm ε (a ⇒ a)
II = app I I

II≡I : get (II {a = ★}) ≡ get I
II≡I = refl


SKK : ∀ {a} → Tm ε (a ⇒ a)
SKK {a} = app (app S K) (K {b = a ⇒ a})

SKK≡I : get (SKK {a = ★}) ≡ get I
SKK≡I = refl


SKSK : ∀ {a b} → Tm ε (a ⇒ b ⇒ a)
SKSK = app (app (app S K) S) K

SKSK≡K : get (SKSK {a = ★} {b = ★ ⇒ ★}) ≡ get K
SKSK≡K = refl


flip : ∀ {a b c} → Tm ε ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
flip = lam (lam (lam (app (app (var (pop (pop top))) (var top)) (var (pop top)))))

flipflipK≡K : get (app flip (app flip (K {a = ★} {b = ★ ⇒ ★}))) ≡ get K
flipflipK≡K = refl
