{-# OPTIONS --rewriting #-}

module A201802.WIP.CoquandList where

open import A201801.Prelude
open import A201801.Category

open import A201802.WIP.Bool
open import A201802.WIP.Name


--------------------------------------------------------------------------------


infix 6 _,_⦂_
mutual
  data List (𝔄 : Set) : Set
    where
      ∙ : List 𝔄

      _,_⦂_ : (Ξ : List 𝔄) (x : Name) → 𝔄 → {{_ : T (fresh x Ξ)}}
                                      → List 𝔄

  fresh : ∀ {𝔄} → Name → List 𝔄 → Bool
  fresh x ∙           = true
  fresh x (Ξ , y ⦂ A) = and (x ≠ y) (fresh x Ξ)


--------------------------------------------------------------------------------


infix 4 _∋_⦂_
data _∋_⦂_ {𝔄} : List 𝔄 → Name → 𝔄 → Set
  where
    zero : ∀ {Ξ A x} → {{_ : T (fresh x Ξ)}}
                     → Ξ , x ⦂ A ∋ x ⦂ A

    suc : ∀ {Ξ A B x y} → {{_ : T (fresh y Ξ)}}
                        → Ξ ∋ x ⦂ A
                        → Ξ , y ⦂ B ∋ x ⦂ A


not∋ : ∀ {𝔄 A x} → {Ξ : List 𝔄} {{_ : T (fresh x Ξ)}}
                 → ¬ (Ξ ∋ x ⦂ A)
not∋ {x = x} {{φ}}  zero             with x ≟ x
not∋ {x = x} {{()}} zero             | yes refl
not∋ {x = x} {{φ}}  zero             | no x≢x   = refl ↯ x≢x
not∋ {x = x} {{φ}}  (suc {y = y}  i) with x ≟ y
not∋ {x = x} {{()}} (suc {y = .x} i) | yes refl
not∋ {x = x} {{φ}}  (suc {y = y}  i) | no x≢y   = i ↯ not∋


uniq∋ : ∀ {𝔄 A x} → {Ξ : List 𝔄} (i j : Ξ ∋ x ⦂ A)
                  → i ≡ j
uniq∋ zero    zero    = refl
uniq∋ zero    (suc j) = j ↯ not∋
uniq∋ (suc i) zero    = i ↯ not∋
uniq∋ (suc i) (suc j) = suc & uniq∋ i j


--------------------------------------------------------------------------------


infix 4 _⊇_
data _⊇_ {𝔄} : List 𝔄 → List 𝔄 → Set
  where
    done : ∀ {Ξ} → Ξ ⊇ ∙

    step : ∀ {Ξ Ξ′ A x} → {{_ : T (fresh x Ξ)}}
                        → Ξ′ ⊇ Ξ → Ξ′ ∋ x ⦂ A
                        → Ξ′ ⊇ Ξ , x ⦂ A


put⊇ : ∀ {𝔄} → {Ξ Ξ′ : List 𝔄}
             → (∀ {A x} → Ξ ∋ x ⦂ A → Ξ′ ∋ x ⦂ A)
             → Ξ′ ⊇ Ξ
put⊇ {Ξ = ∙}         f = done
put⊇ {Ξ = Ξ , x ⦂ A} f = step (put⊇ (f ∘ suc)) (f zero)


get⊇ : ∀ {𝔄 A x} → {Ξ Ξ′ : List 𝔄}
                 → Ξ′ ⊇ Ξ → Ξ ∋ x ⦂ A
                 → Ξ′ ∋ x ⦂ A
get⊇ (step η i) zero    = i
get⊇ (step η i) (suc j) = get⊇ η j


uniq⊇ : ∀ {𝔄} → {Ξ Ξ′ : List 𝔄}
              → (η₁ η₂ : Ξ′ ⊇ Ξ)
              → η₁ ≡ η₂
uniq⊇ done       done        = refl
uniq⊇ (step c i) (step c′ j) = step & uniq⊇ c c′ ⊗ uniq∋ i j


drop⊇ : ∀ {𝔄 A x} → {Ξ Ξ′ : List 𝔄} {{_ : T (fresh x Ξ′)}}
                  → Ξ′ ⊇ Ξ
                  → Ξ′ , x ⦂ A ⊇ Ξ
drop⊇ done       = done
drop⊇ (step η i) = step (drop⊇ η) (suc i)


keep⊇ : ∀ {𝔄 A x} → {Ξ Ξ′ : List 𝔄} {{_ : T (fresh x Ξ′)}} {{_ : T (fresh x Ξ)}}
                  → Ξ′ ⊇ Ξ
                  → Ξ′ , x ⦂ A ⊇ Ξ , x ⦂ A
keep⊇ η = step (drop⊇ η) zero


id⊇ : ∀ {𝔄} → {Ξ : List 𝔄}
            → Ξ ⊇ Ξ
id⊇ = put⊇ id


_∘⊇_ : ∀ {𝔄} → {Ξ Ξ′ Ξ″ : List 𝔄}
             → Ξ′ ⊇ Ξ → Ξ″ ⊇ Ξ′
             → Ξ″ ⊇ Ξ
η₁ ∘⊇ η₂ = put⊇ (get⊇ η₂ ∘ get⊇ η₁)


--------------------------------------------------------------------------------


lid∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
              → (η : Ξ′ ⊇ Ξ)
              → id⊇ ∘⊇ η ≡ η
lid∘⊇ η = uniq⊇ (id⊇ ∘⊇ η) η


rid∘⊇ : ∀ {X} → {Ξ Ξ′ : List X}
              → (η : Ξ′ ⊇ Ξ)
              → η ∘⊇ id⊇ ≡ η
rid∘⊇ η = uniq⊇ (η ∘⊇ id⊇) η

assoc∘⊇ : ∀ {X} → {Ξ Ξ′ Ξ″ Ξ‴ : List X}
                → (η₁ : Ξ′ ⊇ Ξ) (η₂ : Ξ″ ⊇ Ξ′) (η₃ : Ξ‴ ⊇ Ξ″)
                → (η₁ ∘⊇ η₂) ∘⊇ η₃ ≡ η₁ ∘⊇ (η₂ ∘⊇ η₃)
assoc∘⊇ η₁ η₂ η₃ = uniq⊇ ((η₁ ∘⊇ η₂) ∘⊇ η₃) (η₁ ∘⊇ (η₂ ∘⊇ η₃))


instance
  𝐑𝐞𝐧 : ∀ {𝔄} → Category (List 𝔄) _⊇_
  𝐑𝐞𝐧 = record
          { id     = id⊇
          ; _∘_    = _∘⊇_
          ; lid∘   = lid∘⊇
          ; rid∘   = rid∘⊇
          ; assoc∘ = assoc∘⊇
          }


--------------------------------------------------------------------------------


data All {𝔄} (𝔓 : 𝔄 → Set) : List 𝔄 → Set
  where
    ∙ : All 𝔓 ∙

    _,_ : ∀ {Ξ A x} → All 𝔓 Ξ → 𝔓 A → {{_ : T (fresh x Ξ)}}
                    → All 𝔓 (Ξ , x ⦂ A)


get : ∀ {𝔄 𝔓 A x} → {Ξ : List 𝔄}
                  → All 𝔓 Ξ → Ξ ∋ x ⦂ A
                  → 𝔓 A
get (ξ , a) zero    = a
get (ξ , b) (suc i) = get ξ i


maps : ∀ {𝔄 𝔓 𝔔} → {Ξ : List 𝔄}
                 → (∀ {A} → 𝔓 A → 𝔔 A) → All 𝔓 Ξ
                 → All 𝔔 Ξ
maps 𝔣 ∙       = ∙
maps 𝔣 (ξ , a) = maps 𝔣 ξ , 𝔣 a


--------------------------------------------------------------------------------
