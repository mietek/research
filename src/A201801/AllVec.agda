{-# OPTIONS --rewriting #-}

module A201801.AllVec where

open import A201801.Prelude
open import A201801.Vec


--------------------------------------------------------------------------------


data All {X} (P : X → Set) : ∀ {n} → Vec X n → Set
  where
    ∙   : All P ∙
    _,_ : ∀ {n Ξ A} → All P {n} Ξ → P A → All P (Ξ , A)


maps : ∀ {X P Q n} → {Ξ : Vec X n}
                   → (∀ {A} → P A → Q A) → All P Ξ
                   → All Q Ξ
maps f ∙       = ∙
maps f (ξ , a) = maps f ξ , f a


--------------------------------------------------------------------------------


get : ∀ {X P A n I} → {Ξ : Vec X n}
                    → All P Ξ → Ξ ∋⟨ I ⟩ A
                    → P A
get (ξ , a) zero    = a
get (ξ , b) (suc i) = get ξ i


gets : ∀ {X P n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                      → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ
                      → All P Ξ
gets ξ       done     = ∙
gets (ξ , b) (drop η) = gets ξ η
gets (ξ , a) (keep η) = gets ξ η , a


--------------------------------------------------------------------------------


infix 4 _⊇◇⟨_⟩_
data _⊇◇⟨_⟩_ {X P} : ∀ {n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                                → All P Ξ′ → Ξ′ ⊇⟨ e ⟩ Ξ → All P Ξ → Set
  where
    done : ∙ ⊇◇⟨ done ⟩ ∙

    drop : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , a ⊇◇⟨ drop η ⟩ ξ

    keep : ∀ {A n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
                           {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                        → ξ′ ⊇◇⟨ η ⟩ ξ
                        → ξ′ , a ⊇◇⟨ keep η ⟩ ξ , a


bot⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                 → ξ ⊇◇⟨ bot⊇ ⟩ ∙
bot⊇◇ {ξ = ∙}     = done
bot⊇◇ {ξ = ξ , a} = drop bot⊇◇


id⊇◇ : ∀ {X P n} → {Ξ : Vec X n} {ξ : All P Ξ}
                 → ξ ⊇◇⟨ id⊇ ⟩ ξ
id⊇◇ {ξ = ∙}     = done
id⊇◇ {ξ = ξ , a} = keep id⊇◇


_∘⊇◇_ : ∀ {X P n n′ n″ e₁ e₂} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {Ξ″ : Vec X n″}
                                 {η₁ : Ξ′ ⊇⟨ e₁ ⟩ Ξ} {η₂ : Ξ″ ⊇⟨ e₂ ⟩ Ξ′}
                                 {ξ : All P Ξ} {ξ′ : All P Ξ′} {ξ″ : All P Ξ″}
                              → ξ′ ⊇◇⟨ η₁ ⟩ ξ → ξ″ ⊇◇⟨ η₂ ⟩ ξ′
                              → ξ″ ⊇◇⟨ η₁ ∘⊇ η₂ ⟩ ξ
𝜂₁      ∘⊇◇ done    = 𝜂₁
𝜂₁      ∘⊇◇ drop 𝜂₂ = drop (𝜂₁ ∘⊇◇ 𝜂₂)
drop 𝜂₁ ∘⊇◇ keep 𝜂₂ = drop (𝜂₁ ∘⊇◇ 𝜂₂)
keep 𝜂₁ ∘⊇◇ keep 𝜂₂ = keep (𝜂₁ ∘⊇◇ 𝜂₂)


--------------------------------------------------------------------------------


infix 4 _∋◇⟨_⟩_
data _∋◇⟨_⟩_ {X P} : ∀ {A n I} → {Ξ : Vec X n}
                               → All P Ξ → Ξ ∋⟨ I ⟩ A → P A → Set
  where
    zero : ∀ {n A} → {Ξ : Vec X n} {ξ : All P Ξ} {a : P A}
                   → ξ , a ∋◇⟨ zero ⟩ a

    suc : ∀ {B n I A} → {Ξ : Vec X n} {i : Ξ ∋⟨ I ⟩ A}
                         {a : P A} {b : P B} {ξ : All P Ξ}
                      → ξ ∋◇⟨ i ⟩ a
                      → ξ , b ∋◇⟨ suc i ⟩ a


ren∋◇ : ∀ {X P A n n′ e I} → {Ξ : Vec X n} {Ξ′ : Vec X n′}
                              {η : Ξ′ ⊇⟨ e ⟩ Ξ} {i : Ξ ∋⟨ I ⟩ A}
                              {a : P A} {ξ : All P Ξ} {ξ′ : All P Ξ′}
                           → ξ′ ⊇◇⟨ η ⟩ ξ → ξ ∋◇⟨ i ⟩ a
                           → ξ′ ∋◇⟨ ren∋ η i ⟩ a
ren∋◇ done     𝑖       = 𝑖
ren∋◇ (drop 𝜂) 𝑖       = suc (ren∋◇ 𝜂 𝑖)
ren∋◇ (keep 𝜂) zero    = zero
ren∋◇ (keep 𝜂) (suc 𝑖) = suc (ren∋◇ 𝜂 𝑖)


--------------------------------------------------------------------------------


-- zips : ∀ {X Y P Q n} → {Ξ : Vec X n} {Ψ : Vec Y n}
--                      → All P Ξ → All Q Ψ
--                      → All (\ { (A , B) → P A × Q B }) (zip Ξ Ψ)
-- zips ∙       ∙       = ∙
-- zips (ξ , a) (ψ , b) = zips ξ ψ , (a , b)


-- zips∋₁ : ∀ {X Y P Q n I A} → {Ξ : Vec X n} {Ψ : Vec Y n} {i : Ξ ∋⟨ I ⟩ A}
--                               {ξ : All P Ξ} {ψ : All Q Ψ} {a : P A}
--                            → ξ ∋◇⟨ i ⟩ a
--                            → zips ξ ψ ∋◇⟨ zip∋₁ i ⟩ (a , get ψ (within Ψ i))
-- zips∋₁ {ξ = ξ , a} {ψ , b} zero    = zero
-- zips∋₁ {ξ = ξ , b} {ψ , c} (suc 𝑖) = suc (zips∋₁ 𝑖)


-- zips∋₂ : ∀ {X Y P Q n I A} → {Ξ : Vec X n} {Ψ : Vec Y n} {i : Ψ ∋⟨ I ⟩ A}
--                               {ξ : All P Ξ} {ψ : All Q Ψ} {a : Q A}
--                            → ψ ∋◇⟨ i ⟩ a
--                            → zips ξ ψ ∋◇⟨ zip∋₂ i ⟩ (get ξ (within Ξ i) , a)
-- zips∋₂ {ξ = ξ , b} {ψ , a} zero    = zero
-- zips∋₂ {ξ = ξ , b} {ψ , c} (suc 𝑖) = suc (zips∋₂ 𝑖)


-- --------------------------------------------------------------------------------


-- data All◇ {X P} (𝑃 : ∀ {A : X} → P A → Set)
--               : ∀ {n} → {Ξ : Vec X n} → All P Ξ → Set
--   where
--     ∙ : All◇ 𝑃 ∙

--     _,_ : ∀ {A n} → {Ξ : Vec X n}
--                      {ξ : All P Ξ} {a : P A}
--                   → All◇ 𝑃 ξ → 𝑃 a
--                   → All◇ 𝑃 (ξ , a)


-- get◇ : ∀ {X P n I A} → {Ξ : Vec X n} {a : P A}
--                         {ξ : All P Ξ} {i : Ξ ∋⟨ I ⟩ A}
--                         {𝑃 : ∀ {A} → P A → Set}
--                      → All◇ 𝑃 ξ → ξ ∋◇⟨ i ⟩ a
--                      → 𝑃 a
-- get◇ (𝜉 , 𝑎) zero    = 𝑎
-- get◇ (𝜉 , 𝑏) (suc 𝑖) = get◇ 𝜉 𝑖


-- gets◇ : ∀ {X P n n′ e} → {Ξ : Vec X n} {Ξ′ : Vec X n′} {η : Ξ′ ⊇⟨ e ⟩ Ξ}
--                           {ξ : All P Ξ} {ξ′ : All P Ξ′}
--                           {𝑃 : ∀ {A} → P A → Set}
--                        → All◇ 𝑃 ξ′ → ξ′ ⊇◇⟨ η ⟩ ξ
--                        → All◇ 𝑃 ξ
-- gets◇ ∙       done     = ∙
-- gets◇ (𝜉 , 𝑏) (drop 𝜂) = gets◇ 𝜉 𝜂
-- gets◇ (𝜉 , 𝑎) (keep 𝜂) = gets◇ 𝜉 𝜂 , 𝑎


-- maps◇ : ∀ {X P n} → {Ξ : Vec X n} {Q : X → Set}
--                      {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
--                      {𝑃 : ∀ {A} → P A → Set} {𝑄 : ∀ {A} → Q A → Set}
--                   → (∀ {A} → {a : P A} → 𝑃 a → 𝑄 (f a)) → All◇ 𝑃 ξ
--                   → All◇ 𝑄 (maps f ξ)
-- maps◇ 𝑓 ∙       = ∙
-- maps◇ 𝑓 (𝜉 , 𝑎) = maps◇ 𝑓 𝜉 , 𝑓 𝑎


-- --------------------------------------------------------------------------------
