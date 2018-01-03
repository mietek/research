{-# OPTIONS --rewriting #-}

module Vec where

open import Prelude
open import Fin


data Vec (X : Set) : Nat → Set
  where
    ∙   : Vec X zero
    _,_ : ∀ {n} → Vec X n → X → Vec X (suc n)


len : ∀ {n X} → Vec X n
              → Nat
len {n} Ξ = n

map : ∀ {X Y n} → (X → Y) → Vec X n
                → Vec Y n
map F ∙       = ∙
map F (Ξ , A) = map F Ξ , F A

get : ∀ {X n} → Vec X n → Fin n
              → X
get (Ξ , A) zero    = A
get (Ξ , B) (suc i) = get Ξ i

gets : ∀ {X n n′} → Vec X n′ → n′ ≥ n
                  → Vec X n
gets Ξ       done     = ∙
gets (Ξ , A) (drop e) = gets Ξ e
gets (Ξ , A) (keep e) = gets Ξ e , A

zip : ∀ {X Y n} → Vec X n → Vec Y n
                → Vec (X × Y) n
zip ∙         ∙         = ∙
zip (Ξ₁ , A₁) (Ξ₂ , A₂) = zip Ξ₁ Ξ₂ , (A₁ , A₂)


infix 4 _⊇⟨_⟩_
data _⊇⟨_⟩_ {X} : ∀ {n n′} → Vec X n′ → n′ ≥ n → Vec X n → Set
  where
    done : ∙ ⊇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ drop e ⟩ Ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ
                        → Ξ′ , A ⊇⟨ keep e ⟩ Ξ , A


bot⊇ : ∀ {X n} → {Ξ : Vec X n}
               → Ξ ⊇⟨ bot≥ ⟩ ∙
bot⊇ {Ξ = ∙}     = done
bot⊇ {Ξ = Ξ , A} = drop bot⊇

id⊇ : ∀ {X n} → {Ξ : Vec X n}
              → Ξ ⊇⟨ id≥ ⟩ Ξ
id⊇ {Ξ = ∙}     = done
id⊇ {Ξ = Ξ , A} = keep id⊇

_∘⊇_ : ∀ {X n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                           → Ξ′ ⊇⟨ e₁ ⟩ Ξ → Ξ″ ⊇⟨ e₂ ⟩ Ξ′
                           → Ξ″ ⊇⟨ e₁ ∘≥ e₂ ⟩ Ξ
η₁      ∘⊇ done    = η₁
η₁      ∘⊇ drop η₂ = drop (η₁ ∘⊇ η₂)
drop η₁ ∘⊇ keep η₂ = drop (η₁ ∘⊇ η₂)
keep η₁ ∘⊇ keep η₂ = keep (η₁ ∘⊇ η₂)


-- NOTE: Uses REWRITE lid∘≥
-- lid∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
--                      → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
--                      → id⊇ ∘⊇ η ≡ η
-- lid∘⊇ done     = refl
-- lid∘⊇ (drop η) = drop & lid∘⊇ η
-- lid∘⊇ (keep η) = keep & lid∘⊇ η

-- NOTE: Uses REWRITE rid∘≥
-- rid∘⊇ : ∀ {X n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
--                      → (η : Ξ′ ⊇⟨ e ⟩ Ξ)
--                      → η ∘⊇ id⊇ ≡ η
-- rid∘⊇ done     = refl
-- rid∘⊇ (drop η) = drop & rid∘⊇ η
-- rid∘⊇ (keep η) = keep & rid∘⊇ η

-- NOTE: Uses REWRITE assoc∘≥
-- assoc∘⊇ : ∀ {X n n′ n″ n‴ e₁ e₂ e₃} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″} {Ξ‴ : Vec X n‴}
--                                     → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (η₃ : Ξ‴ ⊇⟨ e₃ ⟩ Ξ″)
--                                     → η₁ ∘⊇ (η₂ ∘⊇ η₃) ≡ (η₁ ∘⊇ η₂) ∘⊇ η₃
-- assoc∘⊇ η₁        η₂        done      = refl
-- assoc∘⊇ η₁        η₂        (drop η₃) = drop & assoc∘⊇ η₁ η₂ η₃
-- assoc∘⊇ η₁        (drop η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
-- assoc∘⊇ (drop η₁) (keep η₂) (keep η₃) = drop & assoc∘⊇ η₁ η₂ η₃
-- assoc∘⊇ (keep η₁) (keep η₂) (keep η₃) = keep & assoc∘⊇ η₁ η₂ η₃


infix 4 _∋⟨_⟩_
data _∋⟨_⟩_ {X} : ∀ {n} → Vec X n → Fin n → X → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n}
                   → Ξ , A ∋⟨ zero ⟩ A

    suc : ∀ {B A n i} → {Ξ : Vec X n}
                      → Ξ ∋⟨ i ⟩ A
                      → Ξ , B ∋⟨ suc i ⟩ A


find : ∀ {X n} → (Ξ : Vec X n) (i : Fin n)
               → Ξ ∋⟨ i ⟩ get Ξ i
find (Ξ , A) zero    = zero
find (Ξ , B) (suc i) = suc (find Ξ i)

ren∋ : ∀ {X A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                        → Ξ′ ⊇⟨ e ⟩ Ξ → Ξ ∋⟨ i ⟩ A
                        → Ξ′ ∋⟨ renFin e i ⟩ A
ren∋ done     𝒾       = 𝒾
ren∋ (drop η) 𝒾       = suc (ren∋ η 𝒾)
ren∋ (keep η) zero    = zero
ren∋ (keep η) (suc 𝒾) = suc (ren∋ η 𝒾)

zip∋₁ : ∀ {X Y A₁ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₁ ∋⟨ i ⟩ A₁
                       → zip Ξ₁ Ξ₂ ∋⟨ i ⟩ (A₁ , get Ξ₂ i)
zip∋₁ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₁ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc 𝒾) = suc (zip∋₁ 𝒾)

zip∋₂ : ∀ {X Y A₂ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → Ξ₂ ∋⟨ i ⟩ A₂
                       → zip Ξ₁ Ξ₂ ∋⟨ i ⟩ (get Ξ₁ i , A₂)
zip∋₂ {Ξ₁ = Ξ₁ , A₁} {Ξ₂ , A₂} zero    = zero
zip∋₂ {Ξ₁ = Ξ₁ , B₁} {Ξ₂ , B₂} (suc 𝒾) = suc (zip∋₂ 𝒾)


-- NOTE: Uses REWRITE idrenFin
-- idren∋ : ∀ {X A n i} → {Ξ : Vec X n}
--                      → (𝒾 : Ξ ∋⟨ i ⟩ A)
--                      → ren∋ id⊇ 𝒾 ≡ 𝒾
-- idren∋ zero    = refl
-- idren∋ (suc 𝒾) = suc & idren∋ 𝒾

-- NOTE: Uses REWRITE assocrenFin
-- assocren∋ : ∀ {X A n n′ n″ e₁ e₂ i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
--                                     → (η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ) (η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′) (𝒾 : Ξ ∋⟨ i ⟩ A)
--                                     → ren∋ η₂ (ren∋ η₁ 𝒾) ≡ ren∋ (η₁ ∘⊇ η₂) 𝒾
-- assocren∋ η₁        done      𝒾       = refl
-- assocren∋ η₁        (drop η₂) 𝒾       = suc & assocren∋ η₁ η₂ 𝒾
-- assocren∋ (drop η₁) (keep η₂) 𝒾       = suc & assocren∋ η₁ η₂ 𝒾
-- assocren∋ (keep η₁) (keep η₂) zero    = refl
-- assocren∋ (keep η₁) (keep η₂) (suc 𝒾) = suc & assocren∋ η₁ η₂ 𝒾


data All {X} (P : X → Set) : ∀ {n} → Vec X n → Set
  where
    ∙ : All P ∙

    _,_ : ∀ {n Ξ A} → All P {n} Ξ → P A
                    → All P (Ξ , A)


fromVec : ∀ {X P n} → (Ξ : Vec X n)
                    → (∀ A → P A)
                    → All P Ξ
fromVec ∙       p = ∙
fromVec (Ξ , A) p = fromVec Ξ p , p A

fromVec′ : ∀ {X n} → (Ξ : Vec X n)
                   → All (\ A → ⊤) Ξ
fromVec′ Ξ = fromVec Ξ (\ A → tt)

lookup : ∀ {X P A n i} → {Ξ : Vec X n}
                       → All P Ξ → Ξ ∋⟨ i ⟩ A
                       → P A
lookup (ξ , x) zero    = x
lookup (ξ , y) (suc 𝒾) = lookup ξ 𝒾

mapAll : ∀ {X P Q n} → {Ξ : Vec X n}
                     → (∀ {A} → P A → Q A) → All P Ξ
                     → All Q Ξ
mapAll f ∙       = ∙
mapAll f (ξ , x) = mapAll f ξ , f x

zipAll : ∀ {X Y P Q n} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n}
                       → All P Ξ₁ → All Q Ξ₂
                       → All (\ { (A , B) → P A × Q B }) (zip Ξ₁ Ξ₂)
zipAll ∙         ∙         = ∙
zipAll (ξ₁ , x₁) (ξ₂ , x₂) = zipAll ξ₁ ξ₂ , (x₁ , x₂)


infix 4 _⊇◇⟨_⟩_
data _⊇◇⟨_⟩_ {X P} : ∀ {n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                                → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇◇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , x ⊇◇⟨ drop η ⟩ ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {x : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , x ⊇◇⟨ keep η ⟩ ξ , x


bot⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                  → ξ ⊇◇⟨ bot⊇ ⟩ ∙
bot⊇◇ {ξ = ∙}     = done
bot⊇◇ {ξ = ξ , x} = drop bot⊇◇

id⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                 → ξ ⊇◇⟨ id⊇ ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , x} = keep id⊇◇

_∘⊇◇_ : ∀ {X P n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                 {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′}
                                 {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                              → ξ′ ⊇◇⟨ η₁ ⟩ ξ → ξ″ ⊇◇⟨ η₂ ⟩ ξ′
                              → ξ″ ⊇◇⟨ η₁ ∘⊇ η₂ ⟩ ξ
`η₁      ∘⊇◇ done     = `η₁
`η₁      ∘⊇◇ drop `η₂ = drop (`η₁ ∘⊇◇ `η₂)
drop `η₁ ∘⊇◇ keep `η₂ = drop (`η₁ ∘⊇◇ `η₂)
keep `η₁ ∘⊇◇ keep `η₂ = keep (`η₁ ∘⊇◇ `η₂)


infix 4 _∋◇⟨_⟩_
data _∋◇⟨_⟩_ {X P} : ∀ {A n i} → {Ξ : Vec X n}
                               → All P Ξ → Ξ ∋⟨ i ⟩ A → P A → Set
  where
    zero : ∀ {A n} → {Ξ : Vec X n}
                      {ξ : All P Ξ} {x : P A}
                   → ξ , x ∋◇⟨ zero ⟩ x

    suc : ∀ {B n i A} → {Ξ : Vec X n} {𝒾 : Ξ ∋⟨ i ⟩ A}
                         {y : P B} {ξ : All P Ξ} {x : P A}
                      → ξ ∋◇⟨ 𝒾 ⟩ x
                      → ξ , y ∋◇⟨ suc 𝒾 ⟩ x


ren∋◇ : ∀ {X P A n n′ e i} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                              {ξ : All P Ξ} {ξ′ : All P Ξ′} {x : P A}
                           → ξ′ ⊇◇⟨ η ⟩ ξ → ξ ∋◇⟨ 𝒾 ⟩ x
                           → ξ′ ∋◇⟨ ren∋ η 𝒾 ⟩ x
ren∋◇ done      `𝒾       = `𝒾
ren∋◇ (drop `η) `𝒾       = suc (ren∋◇ `η `𝒾)
ren∋◇ (keep `η) zero     = zero
ren∋◇ (keep `η) (suc `𝒾) = suc (ren∋◇ `η `𝒾)

zip∋◇₁ : ∀ {X Y P Q A₁ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n} {𝒾 : Ξ₁ ∋⟨ i ⟩ A₁}
                               {ξ₁ : All P Ξ₁} {ξ₂ : All Q Ξ₂} {x₁ : P A₁}
                            → ξ₁ ∋◇⟨ 𝒾 ⟩ x₁
                            → zipAll ξ₁ ξ₂ ∋◇⟨ zip∋₁ 𝒾 ⟩ (x₁ , lookup ξ₂ (find Ξ₂ i))
zip∋◇₁ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} zero     = zero
zip∋◇₁ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} (suc `𝒾) = suc (zip∋◇₁ `𝒾)

zip∋◇₂ : ∀ {X Y P Q A₂ n i} → {Ξ₁ : Vec X n} {Ξ₂ : Vec Y n} {𝒾 : Ξ₂ ∋⟨ i ⟩ A₂}
                               {ξ₁ : All P Ξ₁} {ξ₂ : All Q Ξ₂} {x₂ : Q A₂}
                            → ξ₂ ∋◇⟨ 𝒾 ⟩ x₂
                            → zipAll ξ₁ ξ₂ ∋◇⟨ zip∋₂ 𝒾 ⟩ (lookup ξ₁ (find Ξ₁ i) , x₂)
zip∋◇₂ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} zero     = zero
zip∋◇₂ {ξ₁ = ξ₁ , x₁} {ξ₂ , x₂} (suc `𝒾) = suc (zip∋◇₂ `𝒾)


data All◇ {X P} (`P : ∀ {A : X} → P A → Set) : ∀ {n} → {Ξ : Vec X n} → All P Ξ → Set
  where
    ∙ : All◇ `P ∙

    _,_ : ∀ {A n} → {Ξ : Vec X n}
                     {ξ : All P Ξ} {x : P A}
                  → All◇ `P ξ → `P x
                  → All◇ `P (ξ , x)


lookup◇ : ∀ {X P A n i} → {Ξ : Vec X n} {x : P A}
                           {ξ : All P Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                           {`P : ∀ {A} → P A → Set}
                        → All◇ `P ξ → ξ ∋◇⟨ 𝒾 ⟩ x
                        → `P x
lookup◇ (`ξ , `x) zero     = `x
lookup◇ (`ξ , `y) (suc `𝒾) = lookup◇ `ξ `𝒾

mapAll◇ : ∀ {X P n} → {Ξ : Vec X n} {Q : X → Set}
                       {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
                       {`P : ∀ {A} → P A → Set} {`Q : ∀ {A} → Q A → Set}
                    → (∀ {A} → {x : P A} → `P x → `Q (f x)) → All◇ `P ξ
                    → All◇ `Q (mapAll f ξ)
mapAll◇ `f ∙         = ∙
mapAll◇ `f (`ξ , `x) = mapAll◇ `f `ξ , `f `x
