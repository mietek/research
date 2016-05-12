module AltArtemovS4 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import AltArtemov as 𝜆∞
import S4


forget : 𝜆∞.Ty → S4.Ty
forget 𝜆∞.⊥      = S4.⊥
forget (A 𝜆∞.⊃ B) = forget A S4.⊃ forget B
forget (A 𝜆∞.∧ B) = forget A S4.∧ forget B
forget (x 𝜆∞.∶ A) = S4.□ forget A


𝜆∞-drop : ∀{A} → 𝜆∞.⊩ A → 𝜆∞.Ty
𝜆∞-drop {A} _ = A

S4-drop : ∀{A} → S4.⊩ A → S4.Ty
S4-drop {A} _ = A


tI : ∀{A} → forget (𝜆∞-drop (𝜆∞.tI {A})) ≡ S4-drop (S4.tI {forget A})
tI = refl

tI² : ∀{A} → forget (𝜆∞-drop (𝜆∞.tI² {A})) ≡ S4-drop (S4.tI² {forget A})
tI² = refl


tK : ∀{A B} → forget (𝜆∞-drop (𝜆∞.tK {A} {B})) ≡ S4-drop (S4.tK {forget A} {forget B})
tK = refl

tK² : ∀{A B} → forget (𝜆∞-drop (𝜆∞.tK² {A} {B})) ≡ S4-drop (S4.tK² {forget A} {forget B})
tK² = refl


tS : ∀{A B C} → forget (𝜆∞-drop (𝜆∞.tS {A} {B} {C})) ≡ S4-drop (S4.tS {forget A} {forget B} {forget C})
tS = refl

tS² : ∀{A B C} → forget (𝜆∞-drop (𝜆∞.tS² {A} {B} {C})) ≡ S4-drop (S4.tS² {forget A} {forget B} {forget C})
tS² = refl


tE13 : ∀{A B} → forget (𝜆∞-drop (𝜆∞.tE13 {A} {B})) ≡ S4-drop (S4.tE13 {forget A} {forget B})
tE13 = refl

tE14 : ∀{x y A B} → forget (𝜆∞-drop (𝜆∞.tE14 {x} {y} {A} {B})) ≡ S4-drop (S4.tE14 {forget A} {forget B})
tE14 = refl
