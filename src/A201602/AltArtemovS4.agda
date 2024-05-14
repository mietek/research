module A201602.AltArtemovS4 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import A201602.AltArtemov as 𝜆∞
import A201602.S4 as S4


forget : 𝜆∞.Ty → S4.Ty
forget 𝜆∞.⊥      = S4.⊥
forget (A 𝜆∞.⊃ B) = forget A S4.⊃ forget B
forget (A 𝜆∞.∧ B) = forget A S4.∧ forget B
forget (A 𝜆∞.∨ B) = forget A S4.∨ forget B
forget (x 𝜆∞.∶ A) = S4.□ forget A


𝜆∞-drop : ∀{A} → 𝜆∞.⊩ A → 𝜆∞.Ty
𝜆∞-drop {A} _ = A

S4-drop : ∀{A} → S4.⊩ A → S4.Ty
S4-drop {A} _ = A


tI : ∀{A} → forget (𝜆∞-drop (𝜆∞.PL.I {A})) ≡ S4-drop (S4.SKICombinators.I {forget A})
tI = refl

tI² : ∀{A} → forget (𝜆∞-drop (𝜆∞.PLExamples.I² {A})) ≡ S4-drop (S4.SKICombinators.I² {forget A})
tI² = refl


tK : ∀{A B} → forget (𝜆∞-drop (𝜆∞.PL.K {A} {B})) ≡ S4-drop (S4.SKICombinators.K {forget A} {forget B})
tK = refl

tK² : ∀{A B} → forget (𝜆∞-drop (𝜆∞.PLExamples.K² {A} {B})) ≡ S4-drop (S4.SKICombinators.K² {forget A} {forget B})
tK² = refl


tS : ∀{A B C} → forget (𝜆∞-drop (𝜆∞.PL.S {A} {B} {C})) ≡ S4-drop (S4.SKICombinators.S {forget A} {forget B} {forget C})
tS = refl

tS² : ∀{A B C} → forget (𝜆∞-drop (𝜆∞.PLExamples.S² {A} {B} {C})) ≡ S4-drop (S4.SKICombinators.S² {forget A} {forget B} {forget C})
tS² = refl


tE13 : ∀{A B} → forget (𝜆∞-drop (𝜆∞.Example1.E13 {A} {B})) ≡ S4-drop (S4.Example1.E13 {forget A} {forget B})
tE13 = refl

tE14 : ∀{x y A B} → forget (𝜆∞-drop (𝜆∞.Example1.E14 {x} {y} {A} {B})) ≡ S4-drop (S4.Example1.E14 {forget A} {forget B})
tE14 = refl
