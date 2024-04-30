{-# OPTIONS --rewriting #-}

module A201706.PreludeVec where

open import A201706.Prelude public


-- Vectors.

data Vec {ℓ} (X : Set ℓ) : Nat → Set ℓ where
  ∅   : Vec X zero
  _,_ : ∀ {n} → Vec X n → X → Vec X (suc n)

length : ∀ {ℓ} {X : Set ℓ} {n} → Vec X n → Nat
length {n = n} L = n

lookup : ∀ {ℓ} {X : Set ℓ} {n} → Vec X n → Fin n → X
lookup ∅       ()
lookup (L , x) zero    = x
lookup (L , y) (suc i) = lookup L i

map : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} {n} → (X → Y) → Vec X n → Vec Y n
map f ∅       = ∅
map f (L , x) = map f L , f x


-- Predicates on vectors.

data All {ℓ ℓ′} {X : Set ℓ} (P : Pred X ℓ′) : ∀ {n} → Pred (Vec X n) ℓ′ where
  ∅   : All P ∅
  _,_ : ∀ {n} {L : Vec X n} {x} →
          All P L → P x → All P (L , x)

mapAll : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {n} {L : Vec X n} {P : Pred X ℓ′} {Q : Pred X ℓ″} →
           (∀ {x} → P x → Q x) → All P L → All Q L
mapAll f ∅       = ∅
mapAll f (A , a) = mapAll f A , f a


-- Order-preserving embeddings on vectors.

infix 3 _⊇⟨_⟩_
data _⊇⟨_⟩_ {ℓ} {X : Set ℓ} : ∀ {n n′} → Vec X n → n ≥ n′ → Vec X n′ → Set ℓ where
  done : ∅ ⊇⟨ done ⟩ ∅
  weak : ∀ {n n′ e} {L : Vec X n} {L′ : Vec X n′} {x} →
           L′ ⊇⟨ e ⟩ L →
           L′ , x ⊇⟨ weak e ⟩ L
  lift : ∀ {n n′ e} {L : Vec X n} {L′ : Vec X n′} {x} →
           L′ ⊇⟨ e ⟩ L →
           L′ , x ⊇⟨ lift e ⟩ L , x

unweak⊇ : ∀ {ℓ} {X : Set ℓ} {n n′ e} {L : Vec X n} {L′ : Vec X n′} {x} →
            L′ ⊇⟨ e ⟩ L , x → L′ ⊇⟨ unweak≥ e ⟩ L
unweak⊇ (weak η) = weak (unweak⊇ η)
unweak⊇ (lift η) = weak η

unlift⊇ : ∀ {ℓ} {X : Set ℓ} {n n′ e} {L : Vec X n} {L′ : Vec X n′} {x} →
            L′ , x ⊇⟨ e ⟩ L , x → L′ ⊇⟨ unlift≥ e ⟩ L
unlift⊇ (weak η) = unweak⊇ η
unlift⊇ (lift η) = η

inf⊇ : ∀ {ℓ} {X : Set ℓ} {n} {L : Vec X n} → L ⊇⟨ inf≥ ⟩ ∅
inf⊇ {L = ∅}     = done
inf⊇ {L = L , x} = weak inf⊇

refl⊇ : ∀ {ℓ} {X : Set ℓ} {n} {L : Vec X n} → L ⊇⟨ refl≥ ⟩ L
refl⊇ {L = ∅}     = done
refl⊇ {L = L , x} = lift refl⊇

trans⊇ : ∀ {ℓ} {X : Set ℓ} {n n′ n″ e e′} {L : Vec X n} {L′ : Vec X n′} {L″ : Vec X n″} →
         L″ ⊇⟨ e′ ⟩ L′ → L′ ⊇⟨ e ⟩ L → L″ ⊇⟨ trans≥ e′ e ⟩ L
trans⊇ done      η        = η
trans⊇ (weak η′) η        = weak (trans⊇ η′ η)
trans⊇ (lift η′) (weak η) = weak (trans⊇ η′ η)
trans⊇ (lift η′) (lift η) = lift (trans⊇ η′ η)

{-# REWRITE idtrans≥₁ #-}
idtrans⊇₁ : ∀ {ℓ} {X : Set ℓ} {n n′ e} {L : Vec X n} {L′ : Vec X n′} →
              (η : L′ ⊇⟨ e ⟩ L) →
              trans⊇ refl⊇ η ≡ η
idtrans⊇₁ done     = refl
idtrans⊇₁ (weak η) = cong weak (idtrans⊇₁ η)
idtrans⊇₁ (lift η) = cong lift (idtrans⊇₁ η)

{-# REWRITE idtrans≥₂ #-}
idtrans⊇₂ : ∀ {ℓ} {X : Set ℓ} {n n′ e} {L : Vec X n} {L′ : Vec X n′} →
              (η : L′ ⊇⟨ e ⟩ L) →
              trans⊇ η refl⊇ ≡ η
idtrans⊇₂ done     = refl
idtrans⊇₂ (weak η) = cong weak (idtrans⊇₂ η)
idtrans⊇₂ (lift η) = cong lift (idtrans⊇₂ η)

{-# REWRITE assoctrans≥ #-}
assoctrans⊇ : ∀ {ℓ} {X : Set ℓ} {n n′ n″ n‴ e e′ e″}
                {L : Vec X n} {L′ : Vec X n′} {L″ : Vec X n″} {L‴ : Vec X n‴} →
                (η″ : L‴ ⊇⟨ e″ ⟩ L″) (η′ : L″ ⊇⟨ e′ ⟩ L′) (η : L′ ⊇⟨ e ⟩ L) →
                trans⊇ η″ (trans⊇ η′ η) ≡ trans⊇ (trans⊇ η″ η′) η
assoctrans⊇ done      η′        η        = refl
assoctrans⊇ (weak η″) η′        η        = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (weak η′) η        = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (lift η′) (weak η) = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (lift η′) (lift η) = cong lift (assoctrans⊇ η″ η′ η)


-- Vector membership.

infix 3 _∋⟨_⟩_
data _∋⟨_⟩_ {ℓ} {X : Set ℓ} : ∀ {n} → Vec X n → Fin n → X → Set ℓ where
  zero : ∀ {n} {L : Vec X n} {x} →
           L , x ∋⟨ zero ⟩ x
  suc  : ∀ {n} {L : Vec X n} {x y i} →
           L ∋⟨ i ⟩ x → L , y ∋⟨ suc i ⟩ x

lookupAll : ∀ {ℓ ℓ′} {X : Set ℓ} {n} {L : Vec X n} {P : Pred X ℓ′} {x i} →
              All P L → L ∋⟨ i ⟩ x → P x
lookupAll (A , a) zero    = a
lookupAll (A , b) (suc 𝒾) = lookupAll A 𝒾

mono∋ : ∀ {ℓ} {X : Set ℓ} {n n′ e} {L : Vec X n} {L′ : Vec X n′} {x i} →
          (η : L′ ⊇⟨ e ⟩ L) → L ∋⟨ i ⟩ x →
          L′ ∋⟨ monoFin e i ⟩ x
mono∋ done     ()
mono∋ (weak η) 𝒾       = suc (mono∋ η 𝒾)
mono∋ (lift η) zero    = zero
mono∋ (lift η) (suc 𝒾) = suc (mono∋ η 𝒾)

{-# REWRITE idmonoFin #-}
idmono∋ : ∀ {ℓ} {X : Set ℓ} {n} {L : Vec X n} {x i} → (𝒾 : L ∋⟨ i ⟩ x) →
            mono∋ refl⊇ 𝒾 ≡ 𝒾
idmono∋ zero    = refl
idmono∋ (suc 𝒾) = cong suc (idmono∋ 𝒾)

{-# REWRITE assocmonoFin #-}
assocmono∋ : ∀ {ℓ} {X : Set ℓ} {n n′ n″ i e e′}
               {L : Vec X n} {L′ : Vec X n′} {L″ : Vec X n″} {x} →
               (η′ : L″ ⊇⟨ e′ ⟩ L′) (η : L′ ⊇⟨ e ⟩ L) (𝒾 : L ∋⟨ i ⟩ x) →
               mono∋ η′ (mono∋ η 𝒾) ≡ mono∋ (trans⊇ η′ η) 𝒾
assocmono∋ done      η        𝒾       = idmono∋ (mono∋ η 𝒾)
assocmono∋ (weak η′) η        𝒾       = cong suc (assocmono∋ η′ η 𝒾)
assocmono∋ (lift η′) (weak η) 𝒾       = cong suc (assocmono∋ η′ η 𝒾)
assocmono∋ (lift η′) (lift η) zero    = refl
assocmono∋ (lift η′) (lift η) (suc 𝒾) = cong suc (assocmono∋ η′ η 𝒾)
