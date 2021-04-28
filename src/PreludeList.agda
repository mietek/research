{-# OPTIONS --rewriting #-}

module PreludeList where

open import Prelude public


-- Lists.

data List {ℓ} (X : Set ℓ) : Set ℓ where
  ∅   : List X
  _,_ : List X → X → List X

inj,₁ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x x′} →
          L List., x ≡ L′ , x′ → L ≡ L′
inj,₁ refl = refl

inj,₂ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x x′} →
          L List., x ≡ L′ , x′ → x ≡ x′
inj,₂ refl = refl

_≟List⟨_⟩_ : ∀ {ℓ} {X : Set ℓ} (L : List X) (_≟X_ : ∀ (x x′ : X) → Dec (x ≡ x′)) (L′ : List X) → Dec (L ≡ L′)
∅       ≟List⟨ _≟X_ ⟩ ∅         = yes refl
∅       ≟List⟨ _≟X_ ⟩ (L′ , x′) = no λ ()
(L , x) ≟List⟨ _≟X_ ⟩ ∅         = no λ ()
(L , x) ≟List⟨ _≟X_ ⟩ (L′ , x′) with L ≟List⟨ _≟X_ ⟩ L′ | x ≟X x′
(L , x) ≟List⟨ _≟X_ ⟩ (L′ , x′) | yes refl | yes refl = yes refl
(L , x) ≟List⟨ _≟X_ ⟩ (L′ , x′) | _        | no x≢x′  = no (x≢x′ ∘ inj,₂)
(L , x) ≟List⟨ _≟X_ ⟩ (L′ , x′) | no L≢L′  | _        = no (L≢L′ ∘ inj,₁)

length : ∀ {ℓ} {X : Set ℓ} → List X → Nat
length ∅       = zero
length (L , x) = suc (length L)

lookup : ∀ {ℓ} {X : Set ℓ} → (L : List X) → Fin (length L) → X
lookup ∅       ()
lookup (L , x) zero    = x
lookup (L , y) (suc i) = lookup L i

map : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → (X → Y) → List X → List Y
map f ∅       = ∅
map f (L , x) = map f L , f x

reduce : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → (Y → X → Y) → Y → List X → Y
reduce f y ∅       = y
reduce f y (L , x) = f (reduce f y L) x


-- Predicates on lists.

data All {ℓ ℓ′} {X : Set ℓ} (P : Pred X ℓ′) : Pred (List X) ℓ′ where
  ∅   : All P ∅
  _,_ : ∀ {L x} → All P L → P x → All P (L , x)

mapAll : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {P : Pred X ℓ′} {Q : Pred X ℓ″} {L} →
           (∀ {x} → P x → Q x) → All P L → All Q L
mapAll f ∅       = ∅
mapAll f (A , a) = mapAll f A , f a

reduceAll : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {P : Pred X ℓ″} {L} →
             (∀ {x} → Y → P x → Y) → Y → All P L → Y
reduceAll f y ∅       = y
reduceAll f y (A , a) = f (reduceAll f y A) a


-- Order-preserving embeddings on lists.

infix 3 _⊇_
data _⊇_ {ℓ} {X : Set ℓ} : List X → List X → Set ℓ where
  done : ∅ ⊇ ∅
  weak : ∀ {L L′ x} → L′ ⊇ L → L′ , x ⊇ L
  lift : ∀ {L L′ x} → L′ ⊇ L → L′ , x ⊇ L , x

injweak⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} {η η′ : L′ ⊇ L} →
             _⊇_.weak {x = x} η ≡ weak η′ → η ≡ η′
injweak⊇ refl = refl

injlift⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} {η η′ : L′ ⊇ L} →
             _⊇_.lift {x = x} η ≡ lift η′ → η ≡ η′
injlift⊇ refl = refl

_≟⊇_ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} → (η η′ : L′ ⊇ L) → Dec (η ≡ η′)
done   ≟⊇ done    = yes refl
weak η ≟⊇ weak η′ with η ≟⊇ η′
weak η ≟⊇ weak η′ | yes refl = yes refl
weak η ≟⊇ weak η′ | no η≢η′  = no (η≢η′ ∘ injweak⊇)
weak η ≟⊇ lift η′ = no λ ()
lift η ≟⊇ weak η′ = no λ ()
lift η ≟⊇ lift η′ with η ≟⊇ η′
lift η ≟⊇ lift η′ | yes refl = yes refl
lift η ≟⊇ lift η′ | no η≢η′  = no (η≢η′ ∘ injlift⊇)

unweak⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} → L′ ⊇ L , x → L′ ⊇ L
unweak⊇ (weak η) = weak (unweak⊇ η)
unweak⊇ (lift η) = weak η

unlift⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} → L′ , x ⊇ L , x → L′ ⊇ L
unlift⊇ (weak η) = unweak⊇ η
unlift⊇ (lift η) = η

inf⊇ : ∀ {ℓ} {X : Set ℓ} {L : List X} → L ⊇ ∅
inf⊇ {L = ∅}     = done
inf⊇ {L = L , x} = weak inf⊇

refl⊇ : ∀ {ℓ} {X : Set ℓ} {L : List X} → L ⊇ L
refl⊇ {L = ∅}     = done
refl⊇ {L = L , x} = lift refl⊇

trans⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ L″ : List X} → L″ ⊇ L′ → L′ ⊇ L → L″ ⊇ L
trans⊇ done      η        = η
trans⊇ (weak η′) η        = weak (trans⊇ η′ η)
trans⊇ (lift η′) (weak η) = weak (trans⊇ η′ η)
trans⊇ (lift η′) (lift η) = lift (trans⊇ η′ η)

idtrans⊇₁ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} →
              (η : L′ ⊇ L) → trans⊇ refl⊇ η ≡ η
idtrans⊇₁ done     = refl
idtrans⊇₁ (weak η) = cong weak (idtrans⊇₁ η)
idtrans⊇₁ (lift η) = cong lift (idtrans⊇₁ η)
{-# REWRITE idtrans⊇₁ #-}

idtrans⊇₂ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} →
              (η : L′ ⊇ L) → trans⊇ η refl⊇ ≡ η
idtrans⊇₂ done     = refl
idtrans⊇₂ (weak η) = cong weak (idtrans⊇₂ η)
idtrans⊇₂ (lift η) = cong lift (idtrans⊇₂ η)

assoctrans⊇ : ∀ {ℓ} {X : Set ℓ} {L L′ L″ L‴ : List X} →
                (η″ : L‴ ⊇ L″) (η′ : L″ ⊇ L′) (η : L′ ⊇ L) →
                trans⊇ η″ (trans⊇ η′ η) ≡ trans⊇ (trans⊇ η″ η′) η
assoctrans⊇ done      η′        η        = refl
assoctrans⊇ (weak η″) η′        η        = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (weak η′) η        = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (lift η′) (weak η) = cong weak (assoctrans⊇ η″ η′ η)
assoctrans⊇ (lift η″) (lift η′) (lift η) = cong lift (assoctrans⊇ η″ η′ η)

-- ⊇→≥ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} → L′ ⊇ L → length L′ ≥ length L
-- ⊇→≥ done     = done
-- ⊇→≥ (weak η) = weak (⊇→≥ η)
-- ⊇→≥ (lift η) = lift (⊇→≥ η)
--
-- inf⊇→≥ : ∀ {ℓ} {X : Set ℓ} (L : List X) → ⊇→≥ (inf⊇ {L = L}) ≡ inf≥
-- inf⊇→≥ ∅       = refl
-- inf⊇→≥ (L , x) = cong weak (inf⊇→≥ L)
--
-- refl⊇→≥ : ∀ {ℓ} {X : Set ℓ} (L : List X) → ⊇→≥ (refl⊇ {L = L}) ≡ refl≥
-- refl⊇→≥ ∅       = refl
-- refl⊇→≥ (L , x) = cong lift (refl⊇→≥ L)
--
-- trans⊇→≥ : ∀ {ℓ} {X : Set ℓ} {L L′ L″ : List X} →
--               (η′ : L″ ⊇ L′) (η : L′ ⊇ L) →
--               trans≥ (⊇→≥ η′) (⊇→≥ η) ≡ ⊇→≥ (trans⊇ η′ η)
-- trans⊇→≥ done      η        = refl
-- trans⊇→≥ (weak η′) η        = cong weak (trans⊇→≥ η′ η)
-- trans⊇→≥ (lift η′) (weak η) = cong weak (trans⊇→≥ η′ η)
-- trans⊇→≥ (lift η′) (lift η) = cong lift (trans⊇→≥ η′ η)


-- List membership.

infix 3 _∋_
data _∋_ {ℓ} {X : Set ℓ} : List X → X → Set ℓ where
  zero : ∀ {L x}   → L , x ∋ x
  suc  : ∀ {L x y} → L ∋ x → L , y ∋ x

injsuc∋ : ∀ {ℓ} {X : Set ℓ} {L : List X} {x y} {𝒾 𝒾′ : L ∋ x} →
            _∋_.suc {y = y} 𝒾 ≡ suc 𝒾′ → 𝒾 ≡ 𝒾′
injsuc∋ refl = refl

_≟∋_ : ∀ {ℓ} {X : Set ℓ} {L : List X} {x} → (𝒾 𝒾′ : L ∋ x) → Dec (𝒾 ≡ 𝒾′)
zero  ≟∋ zero   = yes refl
zero  ≟∋ suc 𝒾′ = no λ ()
suc 𝒾 ≟∋ zero   = no λ ()
suc 𝒾 ≟∋ suc 𝒾′ with 𝒾 ≟∋ 𝒾′
suc 𝒾 ≟∋ suc 𝒾′ | yes refl = yes refl
suc 𝒾 ≟∋ suc 𝒾′ | no 𝒾≢𝒾′  = no (𝒾≢𝒾′ ∘ injsuc∋)

idlookup : ∀ {ℓ} {X : Set ℓ} → (L : List X) (i : Fin (length L)) →
           L ∋ lookup L i
idlookup ∅       ()
idlookup (L , x) zero    = zero
idlookup (L , x) (suc i) = suc (idlookup L i)

lookupAll : ∀ {ℓ ℓ′} {X : Set ℓ} {P : Pred X ℓ′} {L x} →
              All P L → L ∋ x → P x
lookupAll (A , a) zero    = a
lookupAll (A , b) (suc 𝒾) = lookupAll A 𝒾

mono∋ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} →
          L′ ⊇ L → L ∋ x → L′ ∋ x
mono∋ done     ()
mono∋ (weak η) 𝒾       = suc (mono∋ η 𝒾)
mono∋ (lift η) zero    = zero
mono∋ (lift η) (suc 𝒾) = suc (mono∋ η 𝒾)

injmono∋ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} {x} →
             (η : L′ ⊇ L) (𝒾 𝒾′ : L ∋ x) →
             mono∋ η 𝒾 ≡ mono∋ η 𝒾′ → 𝒾 ≡ 𝒾′
injmono∋ done     ()      ()       p
injmono∋ (weak η) 𝒾       𝒾′       p = injmono∋ η 𝒾 𝒾′ (injsuc∋ p)
injmono∋ (lift η) zero    zero     p = refl
injmono∋ (lift η) zero    (suc 𝒾′) ()
injmono∋ (lift η) (suc 𝒾) zero     ()
injmono∋ (lift η) (suc 𝒾) (suc 𝒾′) p = cong suc (injmono∋ η 𝒾 𝒾′ (injsuc∋ p))

idmono∋ : ∀ {ℓ} {X : Set ℓ} {L : List X} {x} →
            (𝒾 : L ∋ x) → mono∋ refl⊇ 𝒾 ≡ 𝒾
idmono∋ zero    = refl
idmono∋ (suc 𝒾) = cong suc (idmono∋ 𝒾)

assocmono∋ : ∀ {ℓ} {X : Set ℓ} {L L′ L″ : List X} {x} →
               (η′ : L″ ⊇ L′) (η : L′ ⊇ L) (𝒾 : L ∋ x) →
               mono∋ η′ (mono∋ η 𝒾) ≡ mono∋ (trans⊇ η′ η) 𝒾
assocmono∋ done      η        𝒾       = idmono∋ (mono∋ η 𝒾)
assocmono∋ (weak η′) η        𝒾       = cong suc (assocmono∋ η′ η 𝒾)
assocmono∋ (lift η′) (weak η) 𝒾       = cong suc (assocmono∋ η′ η 𝒾)
assocmono∋ (lift η′) (lift η) zero    = refl
assocmono∋ (lift η′) (lift η) (suc 𝒾) = cong suc (assocmono∋ η′ η 𝒾)


-- List concatenation.

_⧺_ : ∀ {ℓ} {X : Set ℓ} → List X → List X → List X
L ⧺ ∅       = L
L ⧺ (K , x) = (L ⧺ K) , x

weak⊇⧺ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} → L′ ⊇ L → (K : List X) → L′ ⧺ K ⊇ L
weak⊇⧺ η ∅       = η
weak⊇⧺ η (K , x) = weak (weak⊇⧺ η K)

lift⊇⧺ : ∀ {ℓ} {X : Set ℓ} {L L′ : List X} → L′ ⊇ L → (K : List X) → L′ ⧺ K ⊇ L ⧺ K
lift⊇⧺ η ∅       = η
lift⊇⧺ η (K , x) = lift (lift⊇⧺ η K)

id⊇⧺₁ : ∀ {ℓ} {X : Set ℓ} → (L : List X) → ∅ ⧺ L ⊇ L
id⊇⧺₁ ∅       = done
id⊇⧺₁ (L , x) = lift (id⊇⧺₁ L)

id⊇⧺₂ : ∀ {ℓ} {X : Set ℓ} → (L : List X) → L ⧺ ∅ ⊇ L
id⊇⧺₂ L = refl⊇

weak⊇⧺₁ : ∀ {ℓ} {X : Set ℓ} {L : List X} → (K : List X) → L ⧺ K ⊇ K
weak⊇⧺₁ K = trans⊇ (lift⊇⧺ inf⊇ K) (id⊇⧺₁ K)

weak⊇⧺₂ : ∀ {ℓ} {X : Set ℓ} {L : List X} → (K : List X) → L ⧺ K ⊇ L
weak⊇⧺₂ K = weak⊇⧺ refl⊇ K

idlift⊇⧺ : ∀ {ℓ} {X : Set ℓ} {L : List X} → (K : List X) → lift⊇⧺ {L = L} refl⊇ K ≡ refl⊇
idlift⊇⧺ ∅       = refl
idlift⊇⧺ (K , x) = cong lift (idlift⊇⧺ K)
{-# REWRITE idlift⊇⧺ #-}

assoclift⊇⧺ : ∀ {ℓ} {X : Set ℓ} {L L′ L″ : List X} →
                (η′ : L″ ⊇ L′) (η : L′ ⊇ L) (K : List X) →
                trans⊇ (lift⊇⧺ η′ K) (lift⊇⧺ η K) ≡ lift⊇⧺ (trans⊇ η′ η) K
assoclift⊇⧺ η′ η ∅       = refl
assoclift⊇⧺ η′ η (K , x) = cong lift (assoclift⊇⧺ η′ η K)
{-# REWRITE assoclift⊇⧺ #-}

invert : ∀ {ℓ} {X : Set ℓ} {L K : List X} → L ⊇ K → Σ (List X) (λ K′ → L ⊇ K′)
invert {L = ∅}     {∅}      done     = ∅ , done
invert {L = L , x} {K}      (weak η) = mapΣ (_, x) lift (invert η)
invert {L = L , x} {K , .x} (lift η) = mapΣ id weak (invert η)
