{-# OPTIONS --rewriting #-}

module mi.FOL where

open import Agda.Builtin.Equality.Rewrite public

open import mi.Prelude public


----------------------------------------------------------------------------------------------------

-- 1.0. primitive recursive n-ary functions on naturals
-- Troelstra (1973) §1.3.4

mutual
  data Prim : Nat → Set where
    zero : Prim 0
    suc  : Prim 1
    proj : ∀ {n} (i : Fin n) → Prim n
    comp : ∀ {n m} (g : Prim m) (φ : Prim§ n m) → Prim n
    rec  : ∀ {n} (f : Prim n) (g : Prim (suc (suc n))) → Prim (suc n)

  Prim§ : Nat → Nat → Set
  Prim§ n m = Vec (Prim n) m

Nat§ : Nat → Set
Nat§ n = Vec Nat n

Fun : Nat → Set
Fun n = Nat§ n → Nat

Fun§ : Nat → Nat → Set
Fun§ n m = Vec (Fun n) m

#zero : Fun 0
#zero ∙ = zero

#suc : Fun 1
#suc (∙ , x) = suc x

#proj : ∀ {n} → Fin n → Fun n
#proj i ξ = peek i ξ

#comp : ∀ {n m} → Fun m → Fun§ n m → Fun n
#comp g φ ξ = g (for φ (λ f → f ξ))

#rec : ∀ {n} → Fun n → Fun (suc (suc n)) → Fun (suc n)
#rec f g (ξ , zero)  = f ξ
#rec f g (ξ , suc x) = g (ξ , x , #rec f g (ξ , x))

mutual
  ⟦_⟧ : ∀ {n} → Prim n → Fun n
  ⟦ zero ⟧     = #zero
  ⟦ suc ⟧      = #suc
  ⟦ proj i ⟧   = #proj i
  ⟦ comp g φ ⟧ = #comp ⟦ g ⟧ ⟦ φ ⟧§
  ⟦ rec f g ⟧  = #rec ⟦ f ⟧ ⟦ g ⟧

  ⟦_⟧§ : ∀ {n m} → Prim§ n m → Fun§ n m
  ⟦ ∙ ⟧§     = ∙
  ⟦ φ , f ⟧§ = ⟦ φ ⟧§ , ⟦ f ⟧


----------------------------------------------------------------------------------------------------

-- 1.1. some primitive recursive n-ary functions on naturals
-- Troelstra and van Dalen (1988) §1.3

module _ where
  open ≡

  const : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X → Y → X
  const x y = x

  ƒconst : ∀ {n} → Nat → Prim n
  ƒconst zero    = comp zero ∙
  ƒconst (suc x) = comp suc (∙ , ƒconst x)

  testconst : ∀ x → ⟦ ƒconst x ⟧ ∙ ≡ const {Y = Nat§ 0} x ∙
  testconst zero    = refl
  testconst (suc x) = suc & testconst x

  ƒadd : Prim 2
  ƒadd = rec (proj 0)
           (comp suc (∙ , proj 0))

  testadd : ∀ x y → ⟦ ƒadd ⟧ (∙ , y , x) ≡ x + y
  testadd zero    y = refl
  testadd (suc x) y = suc & testadd x y

  ƒmul : Prim 2
  ƒmul = rec (ƒconst 0)
           (comp ƒadd (∙ , proj 0 , proj 2))

  testmul : ∀ x y → ⟦ ƒmul ⟧ (∙ , y , x) ≡ x * y
  testmul zero    y = refl
  testmul (suc x) y = (λ z → ⟦ ƒadd ⟧ (∙ , z , y)) & testmul x y
                    ⋮ testadd y (x * y)

  pred : Nat → Nat
  pred x = x - 1

  ƒpred : Prim 1
  ƒpred = rec (ƒconst 0)
            (proj 1)

  testpred : ∀ x → ⟦ ƒpred ⟧ (∙ , x) ≡ pred x
  testpred zero    = refl
  testpred (suc x) = refl

  -- TODO: subtraction

  -- _-_ : Nat → Nat → Nat
  -- x     - zero  = x
  -- zero  - suc y = zero
  -- suc x - suc y = x - y

  -- _-_ : Nat → Nat → Nat
  -- x - zero  = x
  -- x - suc y = pred (x - y)


----------------------------------------------------------------------------------------------------

-- 2.0. terms, indexed by number of term variables

mutual
  data Tm (k : Nat) : Set where
    ‵tvar : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun  : ∀ {n} (f : Prim n) (τ : Tm§ k n) → Tm k

  -- simultaneous substitutions of terms
  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

-- numeric literals for terms
-- TODO: delete this?
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--       { Constraint = Fin⟨ k >_⟩
--       ; fromNat    = λ n → ‵tvar (Fin◇→Fin n)
--       }

𝟘 : ∀ {k} → Tm k
𝟘 = ‵fun zero ∙

𝕊 : ∀ {k} → Tm k → Tm k
𝕊 t = ‵fun suc (∙ , t)

-- numeric literals for naturals encoded as object-level primitive recursive functions
-- TODO: delete this?
-- Nat→Tm : ∀ {k} → Nat → Tm k
-- Nat→Tm zero    = 𝟘
-- Nat→Tm (suc m) = 𝕊 (Nat→Tm m)
--
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--       { Constraint = λ _ → ⊤
--       ; fromNat    = λ n {{_}} → Nat→Tm n
--       }


----------------------------------------------------------------------------------------------------

-- 2.1. terms: renaming

mutual
  renTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  renTm η (‵tvar i)  = ‵tvar (renFin η i)
  renTm η (‵fun f τ) = ‵fun f (renTm§ η τ)

  renTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  renTm§ η ∙       = ∙
  renTm§ η (τ , t) = renTm§ η τ , renTm η t


----------------------------------------------------------------------------------------------------

-- 2.2. terms: generic lemmas about renaming

wkTm : ∀ {k} → Tm k → Tm (suc k)
wkTm t = renTm (wk≤ id≤) t

wkTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) n
wkTm§ τ = renTm§ (wk≤ id≤) τ

liftTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) (suc n)
liftTm§ τ = wkTm§ τ , ‵tvar zero

varTm§ : ∀ {k k′} → k ≤ k′ → Tm§ k′ k
varTm§ stop      = ∙
varTm§ (wk≤ η)   = wkTm§ (varTm§ η)
varTm§ (lift≤ η) = liftTm§ (varTm§ η)

-- TODO: check if changing this affects anything
idTm§ : ∀ {k} → Tm§ k k
-- idTm§ {k = zero}  = ∙
-- idTm§ {k = suc k} = liftTm§ idTm§
idTm§ = varTm§ id≤

subFin : ∀ {k m} → Tm§ m k → Fin k → Tm m
subFin (σ , s) zero    = s
subFin (σ , s) (suc i) = subFin σ i

module _ where
  open ≡

  eqrenpeekTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (τ : Tm§ k n) →
                  peek i (renTm§ η τ) ≡ renTm η (peek i τ)
  eqrenpeekTm η zero    (τ , t) = refl
  eqrenpeekTm η (suc i) (τ , t) = eqrenpeekTm η i τ

  eqrenpokeTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (s : Tm k) (τ : Tm§ k n) →
                  poke i (renTm η s) (renTm§ η τ) ≡ renTm§ η (poke i s τ)
  eqrenpokeTm η zero    s (τ , t) = refl
  eqrenpokeTm η (suc i) s (τ , t) = (_, renTm η t) & eqrenpokeTm η i s τ

  eqrenforTm : ∀ {k k′ n m} (η : k ≤ k′) (φ : Prim§ n m) (τ : Tm§ k n) →
                 for φ (λ f → ‵fun f (renTm§ η τ)) ≡ renTm§ η (for φ (λ f → ‵fun f τ))
  eqrenforTm η ∙       τ = refl
  eqrenforTm η (φ , f) τ = (_, ‵fun f (renTm§ η τ)) & eqrenforTm η φ τ


----------------------------------------------------------------------------------------------------

-- 2.3. terms: substitution

mutual
  subTm : ∀ {k m} → Tm§ m k → Tm k → Tm m
  subTm σ (‵tvar i)  = subFin σ i
  subTm σ (‵fun f τ) = ‵fun f (subTm§ σ τ)

  subTm§ : ∀ {k m n} → Tm§ m k → Tm§ k n → Tm§ m n
  subTm§ σ ∙       = ∙
  subTm§ σ (τ , t) = subTm§ σ τ , subTm σ t


----------------------------------------------------------------------------------------------------

-- 2.4. terms: generic lemmas about substitution

_[_/0]Tm : ∀ {k} → Tm (suc k) → Tm k → Tm k
t [ s /0]Tm = subTm (idTm§ , s) t

_[_/1]Tm : ∀ {k} → Tm (suc (suc k)) → Tm (suc k) → Tm (suc k)
t [ s /1]Tm = subTm (wkTm§ idTm§ , s , ‵tvar zero) t

getTm§ : ∀ {k n n′} → n ≤ n′ → Tm§ k n′ → Tm§ k n
getTm§ stop      τ       = τ
getTm§ (wk≤ η)   (τ , t) = getTm§ η τ
getTm§ (lift≤ η) (τ , t) = getTm§ η τ , t


----------------------------------------------------------------------------------------------------

-- 2.5. terms: fundamental lemmas about renaming

module _ where
  open ≡

  mutual
    idrenTm : ∀ {k} (t : Tm k) → renTm id≤ t ≡ t
    idrenTm (‵tvar i)  = ‵tvar & idrenFin i
    idrenTm (‵fun f τ) = ‵fun f & idrenTm§ τ

    idrenTm§ : ∀ {k n} (τ : Tm§ k n) → renTm§ id≤ τ ≡ τ
    idrenTm§ ∙       = refl
    idrenTm§ (τ , t) = _,_ & idrenTm§ τ ⊗ idrenTm t

  mutual
    comprenTm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (t : Tm k) →
                  renTm (η′ ∘≤ η) t ≡ renTm η′ (renTm η t)
    comprenTm η′ η (‵tvar i)  = ‵tvar & comprenFin η′ η i
    comprenTm η′ η (‵fun f τ) = ‵fun f & comprenTm§ η′ η τ

    comprenTm§ : ∀ {k k′ k″ n} (η′ : k′ ≤ k″) (η : k ≤ k′) (τ : Tm§ k n) →
                   renTm§ (η′ ∘≤ η) τ ≡ renTm§ η′ (renTm§ η τ)
    comprenTm§ η′ η ∙       = refl
    comprenTm§ η′ η (τ , t) = _,_ & comprenTm§ η′ η τ ⊗ comprenTm η′ η t

  ridrenTm : ∀ {k k′} (η : k ≤ k′) (i : Fin k) → renTm η (‵tvar i) ≡ ‵tvar (renFin η i)
  ridrenTm η i = refl

  ridsubTm : ∀ {k m} (σ : Tm§ m k) (i : Fin k) → subTm σ (‵tvar i) ≡ subFin σ i
  ridsubTm σ i = refl


----------------------------------------------------------------------------------------------------

-- 2.6. terms: interaction of renaming and substitution (part 1)
-- TODO: presheaf with subFin?

module _ where
  open ≡

  eqwkrenTm : ∀ {k k′} (η : k ≤ k′) (t : Tm k) →
                renTm (lift≤ η) (wkTm t) ≡ wkTm (renTm η t)
  eqwkrenTm η t = comprenTm (lift≤ η) (wk≤ id≤) t ⁻¹
                ⋮ (λ ~η → renTm (wk≤ ~η) t) & (rid≤ η ⋮ lid≤ η ⁻¹)
                ⋮ comprenTm (wk≤ id≤) η t

  eqwkrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
                 renTm§ (lift≤ η) (wkTm§ τ) ≡ wkTm§ (renTm§ η τ)
  eqwkrenTm§ η ∙       = refl
  eqwkrenTm§ η (τ , t) = _,_ & eqwkrenTm§ η τ ⊗ eqwkrenTm η t

  eqliftrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
                   renTm§ (lift≤ η) (liftTm§ τ) ≡ liftTm§ (renTm§ η τ)
  eqliftrenTm§ η τ = _,_ & eqwkrenTm§ η τ ⊗ ridrenTm (lift≤ η) zero

  ridrenTm§ : ∀ {k k′} (η : k ≤ k′) → renTm§ η idTm§ ≡ varTm§ η
  ridrenTm§ stop      = refl
  ridrenTm§ (wk≤ η)   = (λ ~η → renTm§ (wk≤ ~η) idTm§) & lid≤ η ⁻¹
                      ⋮ comprenTm§ (wk≤ id≤) η idTm§
                      ⋮ wkTm§ & ridrenTm§ η
  ridrenTm§ (lift≤ η) = _,_
                          & ( eqwkrenTm§ η idTm§
                            ⋮ wkTm§ & ridrenTm§ η
                            )
                          ⊗ ridrenTm (lift≤ η) zero

  eqrensubFin : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (i : Fin k) →
                  subFin (renTm§ η σ) i ≡ renTm η (subFin σ i)
  eqrensubFin η (σ , s) zero    = refl
  eqrensubFin η (σ , s) (suc i) = eqrensubFin η σ i

  eqsubrenFin : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (i : Fin k) →
                  subFin (getTm§ η σ) i ≡ subFin σ (renFin η i)
  eqsubrenFin ∙       stop      i       = refl
  eqsubrenFin (σ , s) (wk≤ η)   i       = eqsubrenFin σ η i
  eqsubrenFin (σ , s) (lift≤ η) zero    = refl
  eqsubrenFin (σ , s) (lift≤ η) (suc i) = eqsubrenFin σ η i

  idsubFin : ∀ {k} (i : Fin k) → subFin idTm§ i ≡ ‵tvar i
  idsubFin zero    = refl
  idsubFin (suc i) = eqrensubFin (wk≤ id≤) idTm§ i
                   ⋮ wkTm & idsubFin i
                   ⋮ ridrenTm (wk≤ id≤) i
                   ⋮ (λ ~i → ‵tvar (suc ~i)) & idrenFin i

  compsubFin : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (i : Fin k) →
                 subFin (subTm§ σ′ σ) i ≡ subTm σ′ (subFin σ i)
  compsubFin σ′ (σ , s) zero    = refl
  compsubFin σ′ (σ , s) (suc i) = compsubFin σ′ σ i

  idgetTm§ : ∀ {k n} (τ : Tm§ k n) → getTm§ id≤ τ ≡ τ
  idgetTm§ ∙       = refl
  idgetTm§ (τ , t) = (_, t) & idgetTm§ τ

  compgetTm§ : ∀ {k n n′ n″} (η : n ≤ n′) (η′ : n′ ≤ n″) (τ : Tm§ k n″) →
                 getTm§ (η′ ∘≤ η) τ ≡ getTm§ η (getTm§ η′ τ)
  compgetTm§ η         stop       ∙       = refl
  compgetTm§ η         (wk≤ η′)   (τ , t) = compgetTm§ η η′ τ
  compgetTm§ (wk≤ η)   (lift≤ η′) (τ , t) = compgetTm§ η η′ τ
  compgetTm§ (lift≤ η) (lift≤ η′) (τ , t) = (_, t) & compgetTm§ η η′ τ

  eqrengetTm§ : ∀ {k k′ n n′} (η : k ≤ k′) (η′ : n ≤ n′) (τ : Tm§ k n′) →
                  getTm§ η′ (renTm§ η τ) ≡ renTm§ η (getTm§ η′ τ)
  eqrengetTm§ η stop       ∙       = refl
  eqrengetTm§ η (wk≤ η′)   (τ , t) = eqrengetTm§ η η′ τ
  eqrengetTm§ η (lift≤ η′) (τ , t) = (_, renTm η t) & eqrengetTm§ η η′ τ

  eqwkgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
                 getTm§ (wk≤ η) (liftTm§ τ) ≡ wkTm§ (getTm§ η τ)
  eqwkgetTm§ η τ = eqrengetTm§ (wk≤ id≤) η τ

  eqliftgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
                   getTm§ (lift≤ η) (liftTm§ τ) ≡ liftTm§ (getTm§ η τ)
  eqliftgetTm§ η τ = (_, ‵tvar zero) & eqwkgetTm§ η τ

  ridgetTm§ : ∀ {k k′} (η : k ≤ k′) → getTm§ η idTm§ ≡ varTm§ η
  ridgetTm§ stop      = refl
  ridgetTm§ (wk≤ η)   = eqrengetTm§ (wk≤ id≤) η idTm§
                      ⋮ wkTm§ & ridgetTm§ η
  ridgetTm§ (lift≤ η) = (_, ‵tvar zero)
                          & ( eqrengetTm§ (wk≤ id≤) η idTm§
                            ⋮ wkTm§ & ridgetTm§ η
                            )


----------------------------------------------------------------------------------------------------

-- 2.7. terms: fundamental lemmas about substitution (part 1)

module _ where
  open ≡

  mutual
    eqrensubTm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (t : Tm k) →
                   subTm (renTm§ η σ) t ≡ renTm η (subTm σ t)
    eqrensubTm η σ (‵tvar i)  = eqrensubFin η σ i
    eqrensubTm η σ (‵fun f τ) = ‵fun f & eqrensubTm§ η σ τ

    eqrensubTm§ : ∀ {k m m′ n} (η : m ≤ m′) (σ : Tm§ m k) (τ : Tm§ k n) →
                    subTm§ (renTm§ η σ) τ ≡ renTm§ η (subTm§ σ τ)
    eqrensubTm§ η σ ∙       = refl
    eqrensubTm§ η σ (τ , t) = _,_ & eqrensubTm§ η σ τ ⊗ eqrensubTm η σ t

  mutual
    eqsubrenTm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (t : Tm k) →
                   subTm (getTm§ η σ) t ≡ subTm σ (renTm η t)
    eqsubrenTm σ η (‵tvar i)  = eqsubrenFin σ η i
    eqsubrenTm σ η (‵fun f τ) = ‵fun f & eqsubrenTm§ σ η τ

    eqsubrenTm§ : ∀ {k k′ m n} (σ : Tm§ m k′) (η : k ≤ k′) (τ : Tm§ k n) →
                    subTm§ (getTm§ η σ) τ ≡ subTm§ σ (renTm§ η τ)
    eqsubrenTm§ σ η ∙       = refl
    eqsubrenTm§ σ η (τ , t) = _,_ & eqsubrenTm§ σ η τ ⊗ eqsubrenTm σ η t

  mutual
    idsubTm : ∀ {k} (t : Tm k) → subTm idTm§ t ≡ t
    idsubTm (‵tvar i)  = idsubFin i
    idsubTm (‵fun f τ) = ‵fun f & lidsubTm§ τ

    lidsubTm§ : ∀ {k n} (τ : Tm§ k n) → subTm§ idTm§ τ ≡ τ
    lidsubTm§ ∙       = refl
    lidsubTm§ (τ , t) = _,_ & lidsubTm§ τ ⊗ idsubTm t


----------------------------------------------------------------------------------------------------

-- 2.8. terms: interaction of renaming and substitution (part 2)

module _ where
  open ≡

  eqsubTm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (t : Tm k) →
              subTm (σ , s) (wkTm t) ≡ subTm σ t
  eqsubTm σ s t = eqsubrenTm (σ , s) (wk≤ id≤) t ⁻¹
                ⋮ (λ ~σ → subTm ~σ t) & idgetTm§ σ

  eqsubTm§ : ∀ {k m n} (σ : Tm§ m k) (s : Tm m) (τ : Tm§ k n) →
               subTm§ (σ , s) (wkTm§ τ) ≡ subTm§ σ τ
  eqsubTm§ σ s ∙       = refl
  eqsubTm§ σ s (τ , t) = _,_ & eqsubTm§ σ s τ ⊗ eqsubTm σ s t

  eqwksubTm : ∀ {k m} (σ : Tm§ m k) (t : Tm k) →
                subTm (liftTm§ σ) (wkTm t) ≡ wkTm (subTm σ t)
  eqwksubTm σ t = eqsubrenTm (liftTm§ σ) (wk≤ id≤) t ⁻¹
                ⋮ (λ ~σ → subTm ~σ t)
                    & ( eqwkgetTm§ id≤ σ
                      ⋮ wkTm§ & idgetTm§ σ
                      )
                ⋮ eqrensubTm (wk≤ id≤) σ t

  eqwksubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
                 subTm§ (liftTm§ σ) (wkTm§ τ) ≡ wkTm§ (subTm§ σ τ)
  eqwksubTm§ σ ∙       = refl
  eqwksubTm§ σ (τ , t) = _,_ & eqwksubTm§ σ τ ⊗ eqwksubTm σ t

  eqliftsubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
                   subTm§ (liftTm§ σ) (liftTm§ τ) ≡ liftTm§ (subTm§ σ τ)
  eqliftsubTm§ σ τ = _,_ & eqwksubTm§ σ τ ⊗ ridsubTm (liftTm§ σ) zero

  ridsubTm§ : ∀ {k m} (σ : Tm§ m k) → subTm§ σ idTm§ ≡ σ
  ridsubTm§ ∙       = refl
  ridsubTm§ (σ , s) = _,_
                        & ( eqsubTm§ σ s idTm§
                          ⋮ ridsubTm§ σ
                          )
                        ⊗ ridsubTm (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 2.9. terms: fundamental lemmas about substitution (part 2)

module _ where
  open ≡

  mutual
    compsubTm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (t : Tm k) →
                  subTm (subTm§ σ′ σ) t ≡ subTm σ′ (subTm σ t)
    compsubTm σ′ σ (‵tvar i)  = compsubFin σ′ σ i
    compsubTm σ′ σ (‵fun f τ) = ‵fun f & asssubTm§ σ′ σ τ ⁻¹

    asssubTm§ : ∀ {k m m′ n} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (τ : Tm§ k n) →
                  subTm§ σ′ (subTm§ σ τ) ≡ subTm§ (subTm§ σ′ σ) τ
    asssubTm§ σ′ σ ∙       = refl
    asssubTm§ σ′ σ (τ , t) = _,_ & asssubTm§ σ′ σ τ ⊗ compsubTm σ′ σ t ⁻¹


----------------------------------------------------------------------------------------------------

-- 2.10. terms: interaction of renaming and substitution (part 3)

module _ where
  open ≡

  eqrencut0Tm : ∀ {k k′} (η : k ≤ k′) (t : Tm (suc k)) (s : Tm k) →
                  renTm (lift≤ η) t [ renTm η s /0]Tm ≡ renTm η (t [ s /0]Tm)
  eqrencut0Tm η t s = eqsubrenTm (idTm§ , renTm η s) (lift≤ η) t ⁻¹
                    ⋮ (λ ~σ → subTm (~σ , renTm η s) t)
                        & ( ridgetTm§ η
                          ⋮ ridrenTm§ η ⁻¹
                          )
                    ⋮ eqrensubTm η (idTm§ , s) t

  eqsubcut0Tm : ∀ {k m} (σ : Tm§ m k) (t : Tm (suc k)) (s : Tm k) →
                  subTm (liftTm§ σ) t [ subTm σ s /0]Tm ≡ subTm σ (t [ s /0]Tm)
  eqsubcut0Tm σ t s = compsubTm (idTm§ , subTm σ s) (liftTm§ σ) t ⁻¹
                    ⋮ (λ ~σ → subTm ~σ t)
                        & ( _,_
                              & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                                ⋮ (λ ~σ → subTm§ ~σ σ) & idgetTm§ idTm§
                                ⋮ lidsubTm§ σ
                                ⋮ ridsubTm§ σ ⁻¹
                                )
                              ⊗ ridsubTm (idTm§ , subTm σ s) zero
                          )
                    ⋮ compsubTm σ (idTm§ , s) t


----------------------------------------------------------------------------------------------------

-- 2.11. category of simultaneous substitutions of terms

module Tm§-Gan (funext : Funext) where
  open Gan funext
  open ≤-Gan funext

  pshrenTm : Presheaf cat≤ 0ℓ
  pshrenTm = record
      { ƒObj = λ k → Tm k
      ; ƒ    = renTm
      ; idƒ  = funext idrenTm
      ; _∘ƒ_ = λ η′ η → funext (comprenTm η′ η)
      }

  pshrenTm§ : Nat → Presheaf cat≤ 0ℓ
  pshrenTm§ n = record
      { ƒObj = λ k → Tm§ k n
      ; ƒ    = renTm§
      ; idƒ  = funext idrenTm§
      ; _∘ƒ_ = λ η′ η → funext (comprenTm§ η′ η)
      }

  pshgetTm§ : Nat → Presheaf (cat≤ ᵒᵖ) 0ℓ
  pshgetTm§ k = record
      { ƒObj = λ n → Tm§ k n
      ; ƒ    = getTm§
      ; idƒ  = funext idgetTm§
      ; _∘ƒ_ = λ η′ η → funext (compgetTm§ η′ η)
      }

  catTm§ : Category 0ℓ 0ℓ
  catTm§ = record
      { Obj  = Nat
      ; _▻_  = λ n k → Tm§ k n -- flipped
      ; id   = idTm§
      ; _∘_  = subTm§
      ; lid▻ = lidsubTm§
      ; rid▻ = ridsubTm§
      ; ass▻ = asssubTm§
      ; ◅ssa = λ τ σ σ′ → asssubTm§ σ′ σ τ ⁻¹
      } ᵒᵖ

  pshsubTm : Presheaf catTm§ 0ℓ
  pshsubTm = record
      { ƒObj = λ k → Tm k
      ; ƒ    = subTm
      ; idƒ  = funext idsubTm
      ; _∘ƒ_ = λ σ′ σ → funext (compsubTm σ′ σ)
      }


----------------------------------------------------------------------------------------------------

-- 3.0. formulas, indexed by number of term variables

infix  19 _‵=_
infix  18 ‵∀_
infix  17 ‵∃_
infixl 16 _‵∧_
infixl 15 _‵∨_
infixr 14 _‵⊃_
data Fm (k : Nat) : Set where
  _‵⊃_ : ∀ (A B : Fm k) → Fm k
  _‵∧_ : ∀ (A B : Fm k) → Fm k
  _‵∨_ : ∀ (A B : Fm k) → Fm k
  ‵∀_  : ∀ (A : Fm (suc k)) → Fm k
  ‵∃_  : ∀ (A : Fm (suc k)) → Fm k
  ‵⊥  : Fm k
  _‵=_ : ∀ (t u : Tm k) → Fm k

-- simultaneous substitutions of formulas
Fm§ : Nat → Set
Fm§ k = List (Fm k)

infixr 13 _‵⫗_
_‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵⊃ ‵⊥

infix 19 _‵≠_
_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- 3.1. formulas: renaming

renFm : ∀ {k k′} → k ≤ k′ → Fm k → Fm k′
renFm η (A ‵⊃ B) = renFm η A ‵⊃ renFm η B
renFm η (A ‵∧ B) = renFm η A ‵∧ renFm η B
renFm η (A ‵∨ B) = renFm η A ‵∨ renFm η B
renFm η (‵∀ A)   = ‵∀ renFm (lift≤ η) A
renFm η (‵∃ A)   = ‵∃ renFm (lift≤ η) A
renFm η ‵⊥      = ‵⊥
renFm η (t ‵= u) = renTm η t ‵= renTm η u

renFm§ : ∀ {k k′} → k ≤ k′ → Fm§ k → Fm§ k′
renFm§ η ∙       = ∙
renFm§ η (Γ , A) = renFm§ η Γ , renFm η A


----------------------------------------------------------------------------------------------------

-- 3.2. formulas: generic lemmas about renaming

wkFm : ∀ {k} → Fm k → Fm (suc k)
wkFm A = renFm (wk≤ id≤) A

wkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
wkFm§ Γ = renFm§ (wk≤ id≤) Γ


----------------------------------------------------------------------------------------------------

-- 3.3. formulas: substitution

subFm : ∀ {k m} → Tm§ m k → Fm k → Fm m
subFm σ (A ‵⊃ B) = subFm σ A ‵⊃ subFm σ B
subFm σ (A ‵∧ B) = subFm σ A ‵∧ subFm σ B
subFm σ (A ‵∨ B) = subFm σ A ‵∨ subFm σ B
subFm σ (‵∀ A)   = ‵∀ subFm (liftTm§ σ) A
subFm σ (‵∃ A)   = ‵∃ subFm (liftTm§ σ) A
subFm σ ‵⊥      = ‵⊥
subFm σ (t ‵= u) = subTm σ t ‵= subTm σ u

subFm§ : ∀ {k m} → Tm§ m k → Fm§ k → Fm§ m
subFm§ σ ∙       = ∙
subFm§ σ (Γ , A) = subFm§ σ Γ , subFm σ A


----------------------------------------------------------------------------------------------------

-- 3.4. formulas: generic lemmas about substitution

_[_/0]Fm : ∀ {k} → Fm (suc k) → Tm k → Fm k
A [ s /0]Fm = subFm (idTm§ , s) A

_[_/1]Fm : ∀ {k} → Fm (suc (suc k)) → Tm (suc k) → Fm (suc k)
A [ s /1]Fm = subFm (wkTm§ idTm§ , s , ‵tvar zero) A


----------------------------------------------------------------------------------------------------

-- 3.5. formulas: fundamental lemmas about renaming

module _ where
  open ≡

  idrenFm : ∀ {k} (A : Fm k) → renFm id≤ A ≡ A
  idrenFm (A ‵⊃ B) = _‵⊃_ & idrenFm A ⊗ idrenFm B
  idrenFm (A ‵∧ B) = _‵∧_ & idrenFm A ⊗ idrenFm B
  idrenFm (A ‵∨ B) = _‵∨_ & idrenFm A ⊗ idrenFm B
  idrenFm (‵∀ A)   = ‵∀_ & idrenFm A
  idrenFm (‵∃ A)   = ‵∃_ & idrenFm A
  idrenFm ‵⊥      = refl
  idrenFm (t ‵= u) = _‵=_ & idrenTm t ⊗ idrenTm u

  comprenFm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (A : Fm k) →
                renFm (η′ ∘≤ η) A ≡ renFm η′ (renFm η A)
  comprenFm η′ η (A ‵⊃ B) = _‵⊃_ & comprenFm η′ η A ⊗ comprenFm η′ η B
  comprenFm η′ η (A ‵∧ B) = _‵∧_ & comprenFm η′ η A ⊗ comprenFm η′ η B
  comprenFm η′ η (A ‵∨ B) = _‵∨_ & comprenFm η′ η A ⊗ comprenFm η′ η B
  comprenFm η′ η (‵∀ A)   = ‵∀_ & comprenFm (lift≤ η′) (lift≤ η) A
  comprenFm η′ η (‵∃ A)   = ‵∃_ & comprenFm (lift≤ η′) (lift≤ η) A
  comprenFm η′ η ‵⊥      = refl
  comprenFm η′ η (t ‵= u) = _‵=_ & comprenTm η′ η t ⊗ comprenTm η′ η u


----------------------------------------------------------------------------------------------------

-- 3.6. formulas: interaction of renaming and substitution (part 1)

module _ where
  open ≡

  idrenFm§ : ∀ {k} (Γ : Fm§ k) → renFm§ id≤ Γ ≡ Γ
  idrenFm§ ∙       = refl
  idrenFm§ (Γ , A) = _,_ & idrenFm§ Γ ⊗ idrenFm A

  comprenFm§ : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (Γ : Fm§ k) →
                 renFm§ (η′ ∘≤ η) Γ ≡ renFm§ η′ (renFm§ η Γ)
  comprenFm§ η′ η ∙       = refl
  comprenFm§ η′ η (Γ , A) = _,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η A

  eqwkrenFm : ∀ {k k′} (η : k ≤ k′) (A : Fm k) →
                renFm (lift≤ η) (wkFm A) ≡ wkFm (renFm η A)
  eqwkrenFm η A = comprenFm (lift≤ η) (wk≤ id≤) A ⁻¹
                ⋮ (λ ~η → renFm (wk≤ ~η) A) & (rid≤ η ⋮ lid≤ η ⁻¹)
                ⋮ comprenFm (wk≤ id≤) η A

  eqwkrenFm§ : ∀ {k k′} (η : k ≤ k′) (Γ : Fm§ k) →
                 renFm§ (lift≤ η) (wkFm§ Γ) ≡ wkFm§ (renFm§ η Γ)
  eqwkrenFm§ η ∙       = refl
  eqwkrenFm§ η (Γ , A) = _,_ & eqwkrenFm§ η Γ ⊗ eqwkrenFm η A


----------------------------------------------------------------------------------------------------

-- 3.7. formulas: fundamental lemmas about substitution (part 1)

module _ where
  open ≡

  mutual
    eqrensubFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm k) →
                   subFm (renTm§ η σ) A ≡ renFm η (subFm σ A)
    eqrensubFm η σ (A ‵⊃ B) = _‵⊃_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
    eqrensubFm η σ (A ‵∧ B) = _‵∧_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
    eqrensubFm η σ (A ‵∨ B) = _‵∨_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
    eqrensubFm η σ (‵∀ A)   = ‵∀_ & eqrensubliftFm η σ A
    eqrensubFm η σ (‵∃ A)   = ‵∃_ & eqrensubliftFm η σ A
    eqrensubFm η σ ‵⊥      = refl
    eqrensubFm η σ (t ‵= u) = _‵=_ & eqrensubTm η σ t ⊗ eqrensubTm η σ u

    eqrensubliftFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm (suc k)) →
                       subFm (liftTm§ (renTm§ η σ)) A ≡ renFm (lift≤ η) (subFm (liftTm§ σ) A)
    eqrensubliftFm η σ A = (λ ~σ → subFm ~σ A) & eqliftrenTm§ η σ ⁻¹
                         ⋮ eqrensubFm (lift≤ η) (liftTm§ σ) A

  mutual
    eqsubrenFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm k) →
                   subFm (getTm§ η σ) A ≡ subFm σ (renFm η A)
    eqsubrenFm σ η (A ‵⊃ B) = _‵⊃_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
    eqsubrenFm σ η (A ‵∧ B) = _‵∧_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
    eqsubrenFm σ η (A ‵∨ B) = _‵∨_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
    eqsubrenFm σ η (‵∀ A)   = ‵∀_ & eqsubrenliftFm σ η A
    eqsubrenFm σ η (‵∃ A)   = ‵∃_ & eqsubrenliftFm σ η A
    eqsubrenFm σ η ‵⊥      = refl
    eqsubrenFm σ η (t ‵= u) = _‵=_ & eqsubrenTm σ η t ⊗ eqsubrenTm σ η u

    eqsubrenliftFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm (suc k)) →
                       subFm (liftTm§ (getTm§ η σ)) A ≡ subFm (liftTm§ σ) (renFm (lift≤ η) A)
    eqsubrenliftFm σ η A = (λ ~σ → subFm ~σ A) & eqliftgetTm§ η σ ⁻¹
                         ⋮ eqsubrenFm (liftTm§ σ) (lift≤ η) A

  idsubFm : ∀ {k} (A : Fm k) → subFm idTm§ A ≡ A
  idsubFm (A ‵⊃ B) = _‵⊃_ & idsubFm A ⊗ idsubFm B
  idsubFm (A ‵∧ B) = _‵∧_ & idsubFm A ⊗ idsubFm B
  idsubFm (A ‵∨ B) = _‵∨_ & idsubFm A ⊗ idsubFm B
  idsubFm (‵∀ A)   = ‵∀_ & idsubFm A
  idsubFm (‵∃ A)   = ‵∃_ & idsubFm A
  idsubFm ‵⊥      = refl
  idsubFm (t ‵= u) = _‵=_ & idsubTm t ⊗ idsubTm u


----------------------------------------------------------------------------------------------------

-- 3.8. formulas: interaction of renaming and substitution (part 2)

module _ where
  open ≡

  idsubFm§ : ∀ {k} (Δ : Fm§ k) → subFm§ idTm§ Δ ≡ Δ
  idsubFm§ ∙       = refl
  idsubFm§ (Δ , A) = _,_ & idsubFm§ Δ ⊗ idsubFm A

  eqrensubFm§ : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (Γ : Fm§ k) →
                  subFm§ (renTm§ η σ) Γ ≡ renFm§ η (subFm§ σ Γ)
  eqrensubFm§ η σ ∙       = refl
  eqrensubFm§ η σ (Γ , A) = _,_ & eqrensubFm§ η σ Γ ⊗ eqrensubFm η σ A

  eqsubrenFm§ : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (Γ : Fm§ k) →
                  subFm§ (getTm§ η σ) Γ ≡ subFm§ σ (renFm§ η Γ)
  eqsubrenFm§ σ η ∙       = refl
  eqsubrenFm§ σ η (Γ , A) = _,_ & eqsubrenFm§ σ η Γ ⊗ eqsubrenFm σ η A

  eqsubFm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (A : Fm k) →
              subFm (σ , s) (wkFm A) ≡ subFm σ A
  eqsubFm σ s A = eqsubrenFm (σ , s) (wk≤ id≤) A ⁻¹
                ⋮ (λ ~σ → subFm ~σ A) & idgetTm§ σ

  eqsubFm§ : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (Γ : Fm§ k) →
               subFm§ (σ , s) (wkFm§ Γ) ≡ subFm§ σ Γ
  eqsubFm§ σ s ∙       = refl
  eqsubFm§ σ s (Γ , A) = _,_ & eqsubFm§ σ s Γ ⊗ eqsubFm σ s A

  eqwksubFm : ∀ {k m} (σ : Tm§ m k) (A : Fm k) →
                subFm (liftTm§ σ) (wkFm A) ≡ wkFm (subFm σ A)
  eqwksubFm σ A = eqsubrenFm (liftTm§ σ) (wk≤ id≤) A ⁻¹
                ⋮ (λ ~σ → subFm ~σ A)
                    & ( eqwkgetTm§ id≤ σ
                      ⋮ wkTm§ & idgetTm§ σ
                      )
                ⋮ eqrensubFm (wk≤ id≤) σ A

  eqwksubFm§ : ∀ {k m} (σ : Tm§ m k) (Γ : Fm§ k) →
                 subFm§ (liftTm§ σ) (wkFm§ Γ) ≡ wkFm§ (subFm§ σ Γ)
  eqwksubFm§ σ ∙       = refl
  eqwksubFm§ σ (Γ , A) = _,_ & eqwksubFm§ σ Γ ⊗ eqwksubFm σ A


----------------------------------------------------------------------------------------------------

-- 3.9. formulas: fundamental substitution lemmas (part 2)

module _ where
  open ≡

  mutual
    compsubFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm k) →
                  subFm (subTm§ σ′ σ) A ≡ subFm σ′ (subFm σ A)
    compsubFm σ′ σ (A ‵⊃ B) = _‵⊃_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
    compsubFm σ′ σ (A ‵∧ B) = _‵∧_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
    compsubFm σ′ σ (A ‵∨ B) = _‵∨_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
    compsubFm σ′ σ (‵∀ A)   = ‵∀_ & compsubliftFm σ′ σ A
    compsubFm σ′ σ (‵∃ A)   = ‵∃_ & compsubliftFm σ′ σ A
    compsubFm σ′ σ ‵⊥      = refl
    compsubFm σ′ σ (t ‵= u) = _‵=_ & compsubTm σ′ σ t ⊗ compsubTm σ′ σ u

    compsubliftFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm (suc k)) →
                      subFm (liftTm§ (subTm§ σ′ σ)) A ≡ subFm (liftTm§ σ′) (subFm (liftTm§ σ) A)
    compsubliftFm σ′ σ A = (λ ~σ → subFm ~σ A) & eqliftsubTm§ σ′ σ ⁻¹
                         ⋮ compsubFm (liftTm§ σ′) (liftTm§ σ) A


----------------------------------------------------------------------------------------------------

-- 3.10. formulas: interaction of renaming and substitution (part 3)

module _ where
  open ≡

  compsubFm§ : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (Δ : Fm§ k) →
                 subFm§ (subTm§ σ′ σ) Δ ≡ subFm§ σ′ (subFm§ σ Δ)
  compsubFm§ σ′ σ ∙       = refl
  compsubFm§ σ′ σ (Δ , A) = _,_ & compsubFm§ σ′ σ Δ ⊗ compsubFm σ′ σ A

  idcutFm : ∀ {k} (A : Fm (suc k)) → renFm (lift≤ (wk≤ id≤)) A [ ‵tvar zero /0]Fm ≡ A
  idcutFm A = eqsubrenFm (idTm§ , ‵tvar zero) (lift≤ (wk≤ id≤)) A ⁻¹
            ⋮ (λ ~σ → subFm (~σ , ‵tvar zero) A) & idgetTm§ (wkTm§ idTm§)
            ⋮ idsubFm A

  eqrencut0Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm k) →
                  renFm (lift≤ η) A [ renTm η s /0]Fm ≡ renFm η (A [ s /0]Fm)
  eqrencut0Fm η A s = eqsubrenFm (idTm§ , renTm η s) (lift≤ η) A ⁻¹
                    ⋮ (λ ~σ → subFm (~σ , renTm η s) A) & (ridgetTm§ η ⋮ ridrenTm§ η ⁻¹)
                    ⋮ eqrensubFm η (idTm§ , s) A

  eqrencut1Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm (suc k)) →
                  wkFm (renFm (lift≤ η) A) [ renTm (lift≤ η) s /1]Fm ≡
                    renFm (lift≤ η) (wkFm A [ s /1]Fm)
  eqrencut1Fm η A s = subFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                        & eqwkrenFm (lift≤ η) A ⁻¹
                    ⋮ eqsubrenFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                        (lift≤ (lift≤ η)) (wkFm A) ⁻¹
                    ⋮ (λ ~σ → subFm (~σ , renTm (lift≤ η) s , ‵tvar zero) (wkFm A))
                        & ( eqwkgetTm§ η idTm§
                          ⋮ wkTm§ & (ridgetTm§ η ⋮ ridrenTm§ η ⁻¹)
                          ⋮ eqwkrenTm§ η idTm§ ⁻¹
                          )
                    ⋮ eqrensubFm (lift≤ η) (wkTm§ idTm§ , s , ‵tvar zero) (wkFm A)

  eqsubcut0Fm : ∀ {k m} (σ : Tm§ m k) (A : Fm (suc k)) (s : Tm k) →
                  subFm (liftTm§ σ) A [ subTm σ s /0]Fm ≡ subFm σ (A [ s /0]Fm)
  eqsubcut0Fm σ A s = compsubFm (idTm§ , subTm σ s) (liftTm§ σ) A ⁻¹
                    ⋮ (λ ~σ → subFm ~σ A)
                        & ( _,_
                              & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                                ⋮ (λ ~σ → subTm§ ~σ σ) & idgetTm§ idTm§
                                ⋮ lidsubTm§ σ
                                ⋮ ridsubTm§ σ ⁻¹
                                )
                              ⊗ ridsubTm (idTm§ , subTm σ s) zero
                          )
                    ⋮ compsubFm σ (idTm§ , s) A


----------------------------------------------------------------------------------------------------

-- 3.11. formulas: categorical structures

module Fm§-Gan (funext : Funext) where
  open Gan funext
  open ≤-Gan funext
  open Tm§-Gan funext

  pshrenFm : Presheaf cat≤ 0ℓ
  pshrenFm = record
      { ƒObj = λ k → Fm k
      ; ƒ    = renFm
      ; idƒ  = funext idrenFm
      ; _∘ƒ_ = λ η′ η → funext (comprenFm η′ η)
      }

  pshrenFm§ : Presheaf cat≤ 0ℓ
  pshrenFm§ = record
      { ƒObj = λ k → Fm§ k
      ; ƒ    = renFm§
      ; idƒ  = funext idrenFm§
      ; _∘ƒ_ = λ η′ η → funext (comprenFm§ η′ η)
      }

  pshsubFm : Presheaf catTm§ 0ℓ
  pshsubFm = record
      { ƒObj = λ k → Fm k
      ; ƒ    = subFm
      ; idƒ  = funext idsubFm
      ; _∘ƒ_ = λ σ′ σ → funext (compsubFm σ′ σ)
      }

  pshsubFm§ : Presheaf catTm§ 0ℓ
  pshsubFm§ = record
      { ƒObj = λ k → Fm§ k
      ; ƒ    = subFm§
      ; idƒ  = funext idsubFm§
      ; _∘ƒ_ = λ σ′ σ → funext (compsubFm§ σ′ σ)
      }


----------------------------------------------------------------------------------------------------

-- 4.0. derivations, indexed by list of derivation variables

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

infixr 4 _‵$_
infix  3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var     : ∀ {Þ Γ A} (i : Γ ∋ A) → Þ / Γ ⊢ A -- i-th derivation variable
  ‵lam     : ∀ {Þ Γ A B} (d : Þ / Γ , A ⊢ B) → Þ / Γ ⊢ A ‵⊃ B
  _‵$_     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵⊃ B) (e : Þ / Γ ⊢ A) → Þ / Γ ⊢ B
  ‵pair    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) (e : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∧ B
  ‵fst     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ A
  ‵snd     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ B
  ‵left    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) → Þ / Γ ⊢ A ‵∨ B
  ‵right   : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∨ B
  ‵either  : ∀ {Þ Γ A B C} (c : Þ / Γ ⊢ A ‵∨ B) (d : Þ / Γ , A ⊢ C) (e : Þ / Γ , B ⊢ C) →
               Þ / Γ ⊢ C

  --     A(x₀)
  -- --------------
  --   ∀y.A[y/xₒ]
  ‵all     : ∀ {Þ Γ Γ∗ A} (r : Γ∗ ≡ wkFm§ Γ) (d : Þ / Γ∗ ⊢ A) → Þ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵unall   : ∀ {Þ Γ A A∗} (t : Tm k) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ ‵∀ A) → Þ / Γ ⊢ A∗

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵ex      : ∀ {Þ Γ A A∗} (t : Tm k) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ A∗) → Þ / Γ ⊢ ‵∃ A

  --                 A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵letex   : ∀ {Þ Γ Γ∗ A C C∗} (r₁ : Γ∗ ≡ wkFm§ Γ) (r₂ : C∗ ≡ wkFm C) (d : Þ / Γ ⊢ ‵∃ A)
               (e : Þ / Γ∗ , A ⊢ C∗) →
               Þ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵abortHA : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵magicPA : ∀ {Γ A} (d : PA / Γ , ‵¬ A ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl    : ∀ {Þ Γ t} → Þ / Γ ⊢ t ‵= t
  ‵sym     : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ u ‵= t
  ‵trans   : ∀ {Þ Γ s t u} (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ s ‵= u

  ‵cong    : ∀ {Þ n Γ τ τ∗ s t∗} (f : Prim n) (i : Fin n) (r₁ : poke i s τ ≡ τ∗)
               (r₂ : peek i τ ≡ t∗) (d : Þ / Γ ⊢ s ‵= t∗) →
               Þ / Γ ⊢ ‵fun f τ∗ ‵= ‵fun f τ

  ‵dis     : ∀ {Þ Γ t} → Þ / Γ ⊢ 𝕊 t ‵≠ 𝟘

  ‵inj     : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) → Þ / Γ ⊢ t ‵= u

  --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
  -- ------------------------------------
  --              ∀y.A[y/x₀]
  ‵ind     : ∀ {Þ Γ A A∗₁ A∗₂} (r₁ : A [ 𝟘 /0]Fm ≡ A∗₁) (r₂ : wkFm A [ 𝕊 (‵tvar zero) /1]Fm ≡ A∗₂)
               (d : Þ / Γ ⊢ A∗₁) (e : Þ / Γ ⊢ ‵∀ (A ‵⊃ A∗₂)) →
               Þ / Γ ⊢ ‵∀ A

  ‵proj    : ∀ {Þ n Γ τ t∗} (i : Fin n) (r : peek i τ ≡ t∗) → Þ / Γ ⊢ ‵fun (proj i) τ ‵= t∗

  ‵comp    : ∀ {Þ n m Γ τ τ∗} (g : Prim m) (φ : Prim§ n m) (r : for φ (λ f → ‵fun f τ) ≡ τ∗) →
               Þ / Γ ⊢ ‵fun (comp g φ) τ ‵= ‵fun g τ∗

  ‵rec     : ∀ {Þ n Γ τ t} (f : Prim n) (g : Prim (suc (suc n))) →
               Þ / Γ ⊢ ‵fun (rec f g) (τ , 𝟘) ‵= ‵fun f τ ‵∧
                 ‵fun (rec f g) (τ , 𝕊 t) ‵= ‵fun g (τ , t , ‵fun (rec f g) (τ , t))

-- simultaneous substitutions of derivations
infix 3 _/_⊢§_
data _/_⊢§_ {k} (Þ : Theory) (Γ : Fm§ k) : Fm§ k → Set where
  ∙   : Þ / Γ ⊢§ ∙
  _,_ : ∀ {Δ A} (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) → Þ / Γ ⊢§ Δ , A

-- numeric literals for derivations
instance
  number⊢ : ∀ {Þ k} {Γ : Fm§ k} {A} → Number (Þ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
      { Constraint = Γ ∋⟨_⟩ A
      ; fromNat    = λ n → ‵var (∋◇→∋ n)
      }


----------------------------------------------------------------------------------------------------

-- 4.1. rewrite rules against transport hell

module _ where
  open ≡

  idrenliftFin : ∀ {k} (i : Fin (suc k)) → renFin (lift≤ id≤) i ≡ i
  idrenliftFin zero    = refl
  idrenliftFin (suc i) = suc & idrenFin i

  comprenliftFin : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Fin (suc k)) →
                     renFin (lift≤ η′ ∘≤ lift≤ η) i ≡ renFin (lift≤ η′) (renFin (lift≤ η) i)
  comprenliftFin η′ η zero    = refl
  comprenliftFin η′ η (suc i) = suc & comprenFin η′ η i

  mutual
    idrenliftTm : ∀ {k} (t : Tm (suc k)) → renTm (lift≤ id≤) t ≡ t
    idrenliftTm (‵tvar i)  = ‵tvar & idrenliftFin i
    idrenliftTm (‵fun f τ) = ‵fun f & idrenliftTm§ τ

    idrenliftTm§ : ∀ {k n} (τ : Tm§ (suc k) n) → renTm§ (lift≤ id≤) τ ≡ τ
    idrenliftTm§ ∙       = refl
    idrenliftTm§ (τ , t) = _,_ & idrenliftTm§ τ ⊗ idrenliftTm t

  mutual
    comprenliftTm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (t : Tm (suc k)) →
                      renTm (lift≤ η′ ∘≤ lift≤ η) t ≡ renTm (lift≤ η′) (renTm (lift≤ η) t)
    comprenliftTm η′ η (‵tvar i)  = ‵tvar & comprenliftFin η′ η i
    comprenliftTm η′ η (‵fun f τ) = ‵fun f & comprenliftTm§ η′ η τ

    comprenliftTm§ : ∀ {k k′ k″ n} (η′ : k′ ≤ k″) (η : k ≤ k′) (τ : Tm§ (suc k) n) →
                       renTm§ (lift≤ η′ ∘≤ lift≤ η) τ ≡ renTm§ (lift≤ η′) (renTm§ (lift≤ η) τ)
    comprenliftTm§ η′ η ∙       = refl
    comprenliftTm§ η′ η (τ , t) = _,_ & comprenliftTm§ η′ η τ ⊗ comprenliftTm η′ η t

  idrenliftFm : ∀ {k} (A : Fm (suc k)) → renFm (lift≤ id≤) A ≡ A
  idrenliftFm (A ‵⊃ B) = _‵⊃_ & idrenliftFm A ⊗ idrenliftFm B
  idrenliftFm (A ‵∧ B) = _‵∧_ & idrenliftFm A ⊗ idrenliftFm B
  idrenliftFm (A ‵∨ B) = _‵∨_ & idrenliftFm A ⊗ idrenliftFm B
  idrenliftFm (‵∀ A)   = ‵∀_ & idrenliftFm A
  idrenliftFm (‵∃ A)   = ‵∃_ & idrenliftFm A
  idrenliftFm ‵⊥      = refl
  idrenliftFm (t ‵= u) = _‵=_ & idrenliftTm t ⊗ idrenliftTm u

  idrenliftFm§ : ∀ {k} (Γ : Fm§ (suc k)) → renFm§ (lift≤ id≤) Γ ≡ Γ
  idrenliftFm§ ∙       = refl
  idrenliftFm§ (Γ , A) = _,_ & idrenliftFm§ Γ ⊗ idrenliftFm A

  comprenliftFm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (A : Fm (suc k)) →
                    renFm (lift≤ η′ ∘≤ lift≤ η) A ≡ renFm (lift≤ η′) (renFm (lift≤ η) A)
  comprenliftFm η′ η (A ‵⊃ B) = _‵⊃_ & comprenliftFm η′ η A ⊗ comprenliftFm η′ η B
  comprenliftFm η′ η (A ‵∧ B) = _‵∧_ & comprenliftFm η′ η A ⊗ comprenliftFm η′ η B
  comprenliftFm η′ η (A ‵∨ B) = _‵∨_ & comprenliftFm η′ η A ⊗ comprenliftFm η′ η B
  comprenliftFm η′ η (‵∀ A)   = ‵∀_ & comprenliftFm (lift≤ η′) (lift≤ η) A
  comprenliftFm η′ η (‵∃ A)   = ‵∃_ & comprenliftFm (lift≤ η′) (lift≤ η) A
  comprenliftFm η′ η ‵⊥      = refl
  comprenliftFm η′ η (t ‵= u) = _‵=_ & comprenliftTm η′ η t ⊗ comprenliftTm η′ η u

  comprenliftFm§ : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (Γ : Fm§ (suc k)) →
                     renFm§ (lift≤ η′ ∘≤ lift≤ η) Γ ≡ renFm§ (lift≤ η′) (renFm§ (lift≤ η) Γ)
  comprenliftFm§ η′ η ∙       = refl
  comprenliftFm§ η′ η (Γ , A) = _,_ & comprenliftFm§ η′ η Γ ⊗ comprenliftFm η′ η A

{-# REWRITE idrenTm idrenTm§ #-}
{-# REWRITE comprenTm comprenTm§ #-}
{-# REWRITE idrenFm idrenFm§ #-}
{-# REWRITE comprenFm comprenFm§ #-}

{-# REWRITE idrenliftTm idrenliftTm§ #-}
{-# REWRITE comprenliftTm comprenliftTm§ #-}
{-# REWRITE idrenliftFm idrenliftFm§ #-}
{-# REWRITE comprenliftFm comprenliftFm§ #-}


----------------------------------------------------------------------------------------------------

-- 4.2. term renaming of derivation variables
-- TODO: categorical structures with tren∋ and tren⊆?

tren∋ : ∀ {k k′ Γ A} (η : k ≤ k′) → Γ ∋ A → renFm§ η Γ ∋ renFm η A
tren∋ η zero    = zero
tren∋ η (suc i) = suc (tren∋ η i)

module _ where
  open ≡

  idtren∋ : ∀ {k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → tren∋ id≤ i ≡ i
  idtren∋ zero    = refl
  idtren∋ (suc i) = suc & idtren∋ i

  comptren∋ : ∀ {k k′ k″ Γ A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
                tren∋ (η′ ∘≤ η) i ≡ tren∋ η′ (tren∋ η i)
  comptren∋ η′ η zero = refl
  comptren∋ η′ η (suc i) = suc & comptren∋ η′ η i

-- term renaming of order-preserving embeddings
tren⊆ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊆ Γ′ → renFm§ η Γ ⊆ renFm§ η Γ′
tren⊆ η stop      = stop
tren⊆ η (wk⊆ ζ)   = wk⊆ (tren⊆ η ζ)
tren⊆ η (lift⊆ ζ) = lift⊆ (tren⊆ η ζ)

twk⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → wkFm§ Γ ⊆ wkFm§ Γ′
twk⊆ ζ = tren⊆ (wk≤ id≤) ζ

module _ where
  open ≡

  idtren⊆ : ∀ {k} {Γ Γ′ : Fm§ k} (ζ : Γ ⊆ Γ′) → tren⊆ id≤ ζ ≡ ζ
  idtren⊆ stop      = refl
  idtren⊆ (wk⊆ ζ)   = wk⊆ & idtren⊆ ζ
  idtren⊆ (lift⊆ ζ) = lift⊆ & idtren⊆ ζ

  comptren⊆ : ∀ {k k′ k″ Γ Γ′} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                tren⊆ (η′ ∘≤ η) ζ ≡ tren⊆ η′ (tren⊆ η ζ)
  comptren⊆ η′ η stop      = refl
  comptren⊆ η′ η (wk⊆ ζ)   = wk⊆ & comptren⊆ η′ η ζ
  comptren⊆ η′ η (lift⊆ ζ) = lift⊆ & comptren⊆ η′ η ζ

  ridtren⊆ : ∀ {k k′ Γ} (η : k ≤ k′) → tren⊆ {Γ = Γ} η id⊆ ≡ id⊆
  ridtren⊆ {Γ = ∙}     η = refl
  ridtren⊆ {Γ = Γ , A} η = lift⊆ & ridtren⊆ η

  rcomptren⊆ : ∀ {k k′ Γ Γ′ Γ″} (η : k ≤ k′) (ζ′ : Γ′ ⊆ Γ″) (ζ : Γ ⊆ Γ′) →
                 tren⊆ η (ζ′ ∘⊆ ζ) ≡ tren⊆ η ζ′ ∘⊆ tren⊆ η ζ
  rcomptren⊆ η stop       ζ         = refl
  rcomptren⊆ η (wk⊆ ζ′)   ζ         = wk⊆ & rcomptren⊆ η ζ′ ζ
  rcomptren⊆ η (lift⊆ ζ′) (wk⊆ ζ)   = wk⊆ & rcomptren⊆ η ζ′ ζ
  rcomptren⊆ η (lift⊆ ζ′) (lift⊆ ζ) = lift⊆ & rcomptren⊆ η ζ′ ζ


----------------------------------------------------------------------------------------------------

-- 4.3. term renaming of derivations
-- TODO: categorical structures with tren and tren§?

module _ where
  open ≡

  -- TODO: why does rewriting blow up constraint solver here?
  module _ where
    tren : ∀ {Þ k k′ Γ A} (η : k ≤ k′) → Þ / Γ ⊢ A → Þ / renFm§ η Γ ⊢ renFm η A
    tren η (‵var i)         = ‵var (tren∋ η i)
    tren η (‵lam d)         = ‵lam (tren η d)
    tren η (d ‵$ e)         = tren η d ‵$ tren η e
    tren η (‵pair d e)      = ‵pair (tren η d) (tren η e)
    tren η (‵fst d)         = ‵fst (tren η d)
    tren η (‵snd d)         = ‵snd (tren η d)
    tren η (‵left d)        = ‵left (tren η d)
    tren η (‵right d)       = ‵right (tren η d)
    tren η (‵either c d e)  = ‵either (tren η c) (tren η d) (tren η e)

    tren {Γ = Γ} η (‵all r d)
        = ‵all (renFm§ (lift≤ η) & r ⋮ eqwkrenFm§ η Γ) (tren (lift≤ η) d)

    tren η (‵unall {A = A} t r d)
        = ‵unall (renTm η t) (eqrencut0Fm η A t ⋮ renFm η & r) (tren η d)

    tren η (‵ex {A = A} t r d)
        = ‵ex (renTm η t) (eqrencut0Fm η A t ⋮ renFm η & r) (tren η d)

    tren {Γ = Γ} η (‵letex {C = C} r₁ r₂ d e)
        = ‵letex (renFm§ (lift≤ η) & r₁ ⋮ eqwkrenFm§ η Γ) (renFm (lift≤ η) & r₂ ⋮ eqwkrenFm η C)
            (tren η d) (tren (lift≤ η) e)

    tren η (‵abortHA d)     = ‵abortHA (tren η d)
    tren η (‵magicPA d)     = ‵magicPA (tren η d)
    tren η ‵refl            = ‵refl
    tren η (‵sym d)         = ‵sym (tren η d)
    tren η (‵trans d e)     = ‵trans (tren η d) (tren η e)

    tren η (‵cong {τ = τ} {s = s} f i r₁ r₂ d)
        = ‵cong f i (eqrenpokeTm η i s τ ⋮ renTm§ η & r₁) (eqrenpeekTm η i τ ⋮ renTm η & r₂)
            (tren η d)

    tren η ‵dis             = ‵dis
    tren η (‵inj d)         = ‵inj (tren η d)

    tren η (‵ind {A = A} r₁ r₂ d e)
        = ‵ind (eqrencut0Fm η A 𝟘 ⋮ renFm η & r₁)
            (eqrencut1Fm η A (𝕊 (‵tvar zero)) ⋮ renFm (lift≤ η) & r₂) (tren η d) (tren η e)

    tren η (‵proj {τ = τ} i r)
        = ‵proj i (eqrenpeekTm η i τ ⋮ renTm η & r)

    tren η (‵comp {τ = τ} g φ r)
        = ‵comp g φ (eqrenforTm η φ τ ⋮ renTm§ η & r)

    tren η (‵rec f g)       = ‵rec f g

  twk : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / wkFm§ Γ ⊢ wkFm A
  twk d = tren (wk≤ id≤) d

  -- term renaming of simultanous substitutions of derivations
  tren§ : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) → Þ / Γ ⊢§ Δ → Þ / renFm§ η Γ ⊢§ renFm§ η Δ
  tren§ η ∙       = ∙
  tren§ η (δ , d) = tren§ η δ , tren η d

  twk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ} → Þ / Γ ⊢§ Δ → Þ / wkFm§ Γ ⊢§ wkFm§ Δ
  twk§ d = tren§ (wk≤ id≤) d

  idtren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → tren id≤ d ≡ d
  idtren (‵var i)            = ‵var & idtren∋ i
  idtren (‵lam d)            = ‵lam & idtren d
  idtren (d ‵$ e)            = _‵$_ & idtren d ⊗ idtren e
  idtren (‵pair d e)         = ‵pair & idtren d ⊗ idtren e
  idtren (‵fst d)            = ‵fst & idtren d
  idtren (‵snd d)            = ‵snd & idtren d
  idtren (‵left d)           = ‵left & idtren d
  idtren (‵right d)          = ‵right & idtren d
  idtren (‵either c d e)     = ‵either & idtren c ⊗ idtren d ⊗ idtren e
  idtren (‵all r d)          = ‵all & uip _ _ ⊗ idtren d
  idtren (‵unall t r d)      = ‵unall t & uip _ _ ⊗ idtren d
  idtren (‵ex t r d)         = ‵ex t & uip _ _ ⊗ idtren d
  idtren (‵letex r₁ r₂ d e)  = ‵letex & uip _ _ ⊗ uip _ _ ⊗ idtren d ⊗ idtren e
  idtren (‵abortHA d)        = ‵abortHA & idtren d
  idtren (‵magicPA d)        = ‵magicPA & idtren d
  idtren ‵refl               = refl
  idtren (‵sym d)            = ‵sym & idtren d
  idtren (‵trans d e)        = ‵trans & idtren d ⊗ idtren e
  idtren (‵cong f i r₁ r₂ d) = ‵cong f i & uip _ _ ⊗ uip _ _ ⊗ idtren d
  idtren ‵dis                = refl
  idtren (‵inj d)            = ‵inj & idtren d
  idtren (‵ind r₁ r₂ d e)    = ‵ind & uip _ _ ⊗ uip _ _ ⊗ idtren d ⊗ idtren e
  idtren (‵proj i r)         = ‵proj i & uip _ _
  idtren (‵comp g φ r)       = ‵comp g φ & uip _ _
  idtren (‵rec f g)          = refl

  comptren : ∀ {Þ k k′ k″ Γ A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
               tren (η′ ∘≤ η) d ≡ tren η′ (tren η d)
  comptren η′ η (‵var i)            = ‵var & comptren∋ η′ η i
  comptren η′ η (‵lam d)            = ‵lam & comptren η′ η d
  comptren η′ η (d ‵$ e)            = _‵$_ & comptren η′ η d ⊗ comptren η′ η e
  comptren η′ η (‵pair d e)         = ‵pair & comptren η′ η d ⊗ comptren η′ η e
  comptren η′ η (‵fst d)            = ‵fst & comptren η′ η d
  comptren η′ η (‵snd d)            = ‵snd & comptren η′ η d
  comptren η′ η (‵left d)           = ‵left & comptren η′ η d
  comptren η′ η (‵right d)          = ‵right & comptren η′ η d
  comptren η′ η (‵either c d e)     = ‵either & comptren η′ η c ⊗ comptren η′ η d ⊗ comptren η′ η e
  comptren η′ η (‵all r d)          = ‵all
                                        & uip _ _
                                        ⊗ comptren (lift≤ η′) (lift≤ η) d
  comptren η′ η (‵unall t r d)      = ‵unall (renTm (η′ ∘≤ η) t) & uip _ _ ⊗ comptren η′ η d
  comptren η′ η (‵ex t r d)         = ‵ex (renTm (η′ ∘≤ η) t) & uip _ _ ⊗ comptren η′ η d
  comptren η′ η (‵letex r₁ r₂ d e)  = ‵letex
                                        & uip _ _
                                        ⊗ uip _ _
                                        ⊗ comptren η′ η d
                                        ⊗ comptren (lift≤ η′) (lift≤ η) e
  comptren η′ η (‵abortHA d)        = ‵abortHA & comptren η′ η d
  comptren η′ η (‵magicPA d)        = ‵magicPA & comptren η′ η d
  comptren η′ η ‵refl               = refl
  comptren η′ η (‵sym d)            = ‵sym & comptren η′ η d
  comptren η′ η (‵trans d e)        = ‵trans & comptren η′ η d ⊗ comptren η′ η e
  comptren η′ η (‵cong f i r₁ r₂ d) = ‵cong f i & uip _ _ ⊗ uip _ _ ⊗ comptren η′ η d
  comptren η′ η ‵dis                = refl
  comptren η′ η (‵inj d)            = ‵inj & comptren η′ η d
  comptren η′ η (‵ind r₁ r₂ d e)    = ‵ind & uip _ _ ⊗ uip _ _ ⊗ comptren η′ η d ⊗ comptren η′ η e
  comptren η′ η (‵proj i r)         = ‵proj i & uip _ _
  comptren η′ η (‵comp g φ r)       = ‵comp g φ & uip _ _
  comptren η′ η (‵rec f g)          = refl

  idtren§ : ∀ {Þ k} {Γ : Fm§ k} {Δ} (δ : Þ / Γ ⊢§ Δ) → tren§ id≤ δ ≡ δ
  idtren§ ∙       = refl
  idtren§ (δ , d) = _,_ & idtren§ δ ⊗ idtren d

  comptren§ : ∀ {Þ k k′ k″ Γ Δ} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                tren§ (η′ ∘≤ η) δ ≡ tren§ η′ (tren§ η δ)
  comptren§ η′ η ∙       = refl
  comptren§ η′ η (δ , d) = _,_ & comptren§ η′ η δ ⊗ comptren η′ η d

  ridtren : ∀ {Þ k k′ Γ A} (η : k ≤ k′) (i : Γ ∋ A) → tren {Þ = Þ} η (‵var i) ≡ ‵var (tren∋ η i)
  ridtren η i = refl


----------------------------------------------------------------------------------------------------

-- 4.4. derivations: renaming

ren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Þ / Γ ⊢ A → Þ / Γ′ ⊢ A
ren η (‵var i)             = ‵var (ren∋ η i)
ren η (‵lam d)             = ‵lam (ren (lift⊆ η) d)
ren η (d ‵$ e)             = ren η d ‵$ ren η e
ren η (‵pair d e)          = ‵pair (ren η d) (ren η e)
ren η (‵fst d)             = ‵fst (ren η d)
ren η (‵snd d)             = ‵snd (ren η d)
ren η (‵left d)            = ‵left (ren η d)
ren η (‵right d)           = ‵right (ren η d)
ren η (‵either c d e)      = ‵either (ren η c) (ren (lift⊆ η) d) (ren (lift⊆ η) e)
ren η (‵all refl d)        = ‵all refl (ren (twk⊆ η) d)
ren η (‵unall t r d)       = ‵unall t r (ren η d)
ren η (‵ex t r d)          = ‵ex t r (ren η d)
ren η (‵letex refl r₂ d e) = ‵letex refl r₂ (ren η d) (ren (lift⊆ (twk⊆ η)) e)
ren η (‵abortHA d)         = ‵abortHA (ren η d)
ren η (‵magicPA d)         = ‵magicPA (ren (lift⊆ η) d)
ren η ‵refl                = ‵refl
ren η (‵sym d)             = ‵sym (ren η d)
ren η (‵trans d e)         = ‵trans (ren η d) (ren η e)
ren η (‵cong f i r₁ r₂ d)  = ‵cong f i r₁ r₂ (ren η d)
ren η ‵dis                 = ‵dis
ren η (‵inj d)             = ‵inj (ren η d)
ren η (‵ind r₁ r₂ d e)     = ‵ind r₁ r₂ (ren η d) (ren η e)
ren η (‵proj i r)          = ‵proj i r
ren η (‵comp g φ r)        = ‵comp g φ r
ren η (‵rec f g)           = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 4.5. derivations: generic lemmas about renaming

wk : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ A → Þ / Γ , C ⊢ A
wk d = ren (wk⊆ id⊆) d

ren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} {Δ} → Γ ⊆ Γ′ → Þ / Γ ⊢§ Δ → Þ / Γ′ ⊢§ Δ
ren§ η ∙       = ∙
ren§ η (δ , d) = ren§ η δ , ren η d

wk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ
wk§ δ = ren§ (wk⊆ id⊆) δ

lift§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ , C
lift§ δ = wk§ δ , ‵var zero

var§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → Þ / Γ′ ⊢§ Γ
var§ stop      = ∙
var§ (wk⊆ η)   = wk§ (var§ η)
var§ (lift⊆ η) = lift§ (var§ η)

-- TODO: check if changing this affects anything
id§ : ∀ {Þ k} {Γ : Fm§ k} → Þ / Γ ⊢§ Γ
-- id§ {Γ = ∙}     = ∙
-- id§ {Γ = Γ , A} = lift§ id§
id§ = var§ id⊆

sub∋ : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Γ ∋ A → Þ / Ξ ⊢ A
sub∋ (σ , s) zero    = s
sub∋ (σ , s) (suc i) = sub∋ σ i


----------------------------------------------------------------------------------------------------

-- 4.6. derivations: substitution

sub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢ A → Þ / Ξ ⊢ A
sub σ (‵var i)             = sub∋ σ i
sub σ (‵lam d)             = ‵lam (sub (lift§ σ) d)
sub σ (d ‵$ e)             = sub σ d ‵$ sub σ e
sub σ (‵pair d e)          = ‵pair (sub σ d) (sub σ e)
sub σ (‵fst d)             = ‵fst (sub σ d)
sub σ (‵snd d)             = ‵snd (sub σ d)
sub σ (‵left d)            = ‵left (sub σ d)
sub σ (‵right d)           = ‵right (sub σ d)
sub σ (‵either c d e)      = ‵either (sub σ c) (sub (lift§ σ) d) (sub (lift§ σ) e)
sub σ (‵all refl d)        = ‵all refl (sub (twk§ σ) d)
sub σ (‵unall t r d)       = ‵unall t r (sub σ d)
sub σ (‵ex t r d)          = ‵ex t r (sub σ d)
sub σ (‵letex refl r₂ d e) = ‵letex refl r₂ (sub σ d) (sub (lift§ (twk§ σ)) e)
sub σ (‵abortHA d)         = ‵abortHA (sub σ d)
sub σ (‵magicPA d)         = ‵magicPA (sub (lift§ σ) d)
sub σ ‵refl                = ‵refl
sub σ (‵sym d)             = ‵sym (sub σ d)
sub σ (‵trans d e)         = ‵trans (sub σ d) (sub σ e)
sub σ (‵cong f i r₁ r₂ d)  = ‵cong f i r₁ r₂ (sub σ d)
sub σ ‵dis                 = ‵dis
sub σ (‵inj d)             = ‵inj (sub σ d)
sub σ (‵ind r₁ r₂ d e)     = ‵ind r₁ r₂ (sub σ d) (sub σ e)
sub σ (‵proj i r)          = ‵proj i r
sub σ (‵comp g φ r)        = ‵comp g φ r
sub σ (‵rec f g)           = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 4.7. derivations: generic lemmas about substitution

sub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢§ Δ → Þ / Ξ ⊢§ Δ
sub§ σ ∙       = ∙
sub§ σ (δ , d) = sub§ σ δ , sub σ d

_[_/0] : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ , A ⊢ B → Þ / Γ ⊢ A → Þ / Γ ⊢ B
d [ s /0] = sub (id§ , s) d

get§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} → Δ ⊆ Δ′ → Þ / Γ ⊢§ Δ′ → Þ / Γ ⊢§ Δ
get§ stop      δ       = δ
get§ (wk⊆ η)   (δ , d) = get§ η δ
get§ (lift⊆ η) (δ , d) = get§ η δ , d


----------------------------------------------------------------------------------------------------

-- 4.8. derivations: fundamental lemmas about renaming

module _ where
  open ≡

  idren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → ren id⊆ d ≡ d
  idren (‵var i)                = ‵var & idren∋ i
  idren (‵lam d)                = ‵lam & idren d
  idren (d ‵$ e)                = _‵$_ & idren d ⊗ idren e
  idren (‵pair d e)             = ‵pair & idren d ⊗ idren e
  idren (‵fst d)                = ‵fst & idren d
  idren (‵snd d)                = ‵snd & idren d
  idren (‵left d)               = ‵left & idren d
  idren (‵right d)              = ‵right & idren d
  idren (‵either c d e)         = ‵either & idren c ⊗ idren d ⊗ idren e
  idren (‵all refl d)           = ‵all refl
                                    & ( (λ ~η → ren ~η d)
                                          & ridtren⊆ (wk≤ id≤) ⋮ idren d
                                      )
  idren (‵unall t refl d)       = ‵unall t refl & idren d
  idren (‵ex t refl d)          = ‵ex t refl & idren d
  idren (‵letex refl refl d e)  = ‵letex refl refl
                                    & idren d
                                    ⊗ ( (λ ~η → ren (lift⊆ ~η) e)
                                          & ridtren⊆ (wk≤ id≤) ⋮ idren e
                                      )
  idren (‵abortHA d)            = ‵abortHA & idren d
  idren (‵magicPA d)            = ‵magicPA & idren d
  idren ‵refl                   = refl
  idren (‵sym d)                = ‵sym & idren d
  idren (‵trans d e)            = ‵trans & idren d ⊗ idren e
  idren (‵cong f i refl refl d) = ‵cong f i refl refl & idren d
  idren ‵dis                    = refl
  idren (‵inj d)                = ‵inj & idren d
  idren (‵ind refl refl d e)    = ‵ind refl refl & idren d ⊗ idren e
  idren (‵proj i refl)          = refl
  idren (‵comp g φ refl)        = refl
  idren (‵rec f g)              = refl

  compren : ∀ {Þ k} {Γ Γ′ Γ″ : Fm§ k} {A} (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
              ren (η′ ∘⊆ η) d ≡ ren η′ (ren η d)
  compren η′ η (‵var i)                = ‵var & compren∋ η′ η i
  compren η′ η (‵lam d)                = ‵lam & compren (lift⊆ η′) (lift⊆ η) d
  compren η′ η (d ‵$ e)                = _‵$_ & compren η′ η d ⊗ compren η′ η e
  compren η′ η (‵pair d e)             = ‵pair & compren η′ η d ⊗ compren η′ η e
  compren η′ η (‵fst d)                = ‵fst & compren η′ η d
  compren η′ η (‵snd d)                = ‵snd & compren η′ η d
  compren η′ η (‵left d)               = ‵left & compren η′ η d
  compren η′ η (‵right d)              = ‵right & compren η′ η d
  compren η′ η (‵either c d e)         = ‵either
                                           & compren η′ η c
                                           ⊗ compren (lift⊆ η′) (lift⊆ η) d
                                           ⊗ compren (lift⊆ η′) (lift⊆ η) e
  compren η′ η (‵all refl d)           = ‵all refl
                                           & ( (λ ~η → ren ~η d)
                                                 & rcomptren⊆ (wk≤ id≤) η′ η
                                             ⋮ compren (twk⊆ η′) (twk⊆ η) d
                                             )
  compren η′ η (‵unall t refl d)       = ‵unall t refl & compren η′ η d
  compren η′ η (‵ex t refl d)          = ‵ex t refl & compren η′ η d
  compren η′ η (‵letex refl refl d e)  = ‵letex refl refl
                                           & compren η′ η d
                                           ⊗ ( (λ ~η → ren (lift⊆ ~η) e)
                                                 & rcomptren⊆ (wk≤ id≤) η′ η
                                             ⋮ compren (lift⊆ (twk⊆ η′)) (lift⊆ (twk⊆ η)) e
                                             )
  compren η′ η (‵abortHA d)            = ‵abortHA & compren η′ η d
  compren η′ η (‵magicPA d)            = ‵magicPA & compren (lift⊆ η′) (lift⊆ η) d
  compren η′ η ‵refl                   = refl
  compren η′ η (‵sym d)                = ‵sym & compren η′ η d
  compren η′ η (‵trans d e)            = ‵trans & compren η′ η d ⊗ compren η′ η e
  compren η′ η (‵cong f i refl refl d) = ‵cong f i refl refl & compren η′ η d
  compren η′ η ‵dis                    = refl
  compren η′ η (‵inj d)                = ‵inj & compren η′ η d
  compren η′ η (‵ind refl refl d e)    = ‵ind refl refl & compren η′ η d ⊗ compren η′ η e
  compren η′ η (‵proj i refl)          = refl
  compren η′ η (‵comp g φ refl)        = refl
  compren η′ η (‵rec f g)              = refl

  ridren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} (η : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren {Þ = Þ} η (‵var i) ≡ ‵var (ren∋ η i)
  ridren η i = refl

  ridsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
             sub σ (‵var i) ≡ sub∋ σ i
  ridsub σ i = refl


----------------------------------------------------------------------------------------------------

-- 4.9. generalized identity order-preserving embedding of derivation variables

module _ where
  open ≡

  ≡→⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ≡ Γ′ → Γ ⊆ Γ′
  ≡→⊆ refl = id⊆

  -- TODO: why does rewriting blow up constraint solver here?
  module _ where
    shiftall : ∀ {Þ k} {Γ : Fm§ k} {Γ∗ A} (r : Γ∗ ≡ wkFm§ Γ) (d : Þ / Γ∗ ⊢ A) →
                 ‵all {Γ = Γ} refl (ren (≡→⊆ r) d) ≡ ‵all r d
    shiftall refl d = ‵all refl & idren d

    shiftletex : ∀ {Þ k} {Γ : Fm§ k} {Γ∗ A C C∗} (r₁ : Γ∗ ≡ wkFm§ Γ) (r₂ : C∗ ≡ wkFm C)
                   (d : Þ / Γ ⊢ ‵∃ A) (e : Þ / Γ∗ , A ⊢ C∗) →
                   ‵letex {Γ = Γ} {C = C} refl r₂ d (ren (lift⊆ (≡→⊆ r₁)) e) ≡ ‵letex r₁ r₂ d e
    shiftletex refl r₂ d e = ‵letex refl r₂ d & idren e


----------------------------------------------------------------------------------------------------

-- 4.10. interaction between term renaming and derivation renaming
-- TODO: clean this up

module _ where
  open ≅

  hlid⊆ : ∀ {k} {Γ Γ′ ^Γ′ : Fm§ k} (p : Γ′ ≡ ^Γ′) (ζ : Γ ⊆ Γ′) → ≡→⊆ p ∘⊆ ζ ≅ ζ
  hlid⊆ refl ζ = ≡→≅ (lid⊆ ζ)

  hrid⊆ : ∀ {k} {Γ ^Γ Γ′ : Fm§ k} (p : ^Γ ≡ Γ) (ζ : Γ ⊆ Γ′) → ζ ∘⊆ ≡→⊆ p ≅ ζ
  hrid⊆ refl ζ = ≡→≅ (rid⊆ ζ)

  hcomptren⊆ : ∀ {k k′ k″ Γ Γ′} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                 tren⊆ (η′ ∘≤ η) ζ ≅ tren⊆ η′ (tren⊆ η ζ)
  hcomptren⊆ η′ η ζ = ≡→≅ (comptren⊆ η′ η ζ)

  heqwktren⊆ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                 tren⊆ (lift≤ η) (twk⊆ ζ) ≅ twk⊆ (tren⊆ η ζ)
  heqwktren⊆ η ζ = hcomptren⊆ (lift≤ η) (wk≤ id≤) ζ ⁻¹
                 ⋮ (λ ~η → tren⊆ (wk≤ ~η) ζ) & ≡→≅ (rid≤ η ≡.⋮ lid≤ η ≡.⁻¹)
                 ⋮ hcomptren⊆ (wk≤ id≤) η ζ

  -- TODO: rename this
  huntitled1 : ∀ {k k′ Γ Γ′} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                 ≡→⊆ (eqwkrenFm§ η Γ′) ∘⊆ tren⊆ (lift≤ η) (twk⊆ ζ) ≅
                   twk⊆ (tren⊆ η ζ) ∘⊆ ≡→⊆ (eqwkrenFm§ η Γ)
  huntitled1 {Γ = Γ} {Γ′} η ζ = hlid⊆ (eqwkrenFm§ η Γ′) (tren⊆ (lift≤ η) (twk⊆ ζ))
                              ⋮ heqwktren⊆ η ζ
                              ⋮ hrid⊆ (eqwkrenFm§ η Γ) (twk⊆ (tren⊆ η ζ)) ⁻¹

  -- TODO: rename this
  untitled1 : ∀ {k k′ Γ Γ′} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                ≡→⊆ (eqwkrenFm§ η Γ′) ∘⊆ tren⊆ (lift≤ η) (twk⊆ ζ) ≡
                  twk⊆ (tren⊆ η ζ) ∘⊆ ≡→⊆ (eqwkrenFm§ η Γ)
  untitled1 η ζ = ≅→≡ (huntitled1 η ζ)

module _ where
  open ≡

  eqtrenren∋ : ∀ {k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (i : Γ ∋ A) →
                 ren∋ (tren⊆ η ζ) (tren∋ η i) ≡ tren∋ η (ren∋ ζ i)
  eqtrenren∋ η (wk⊆ ζ)   i       = suc & eqtrenren∋ η ζ i
  eqtrenren∋ η (lift⊆ ζ) zero    = refl
  eqtrenren∋ η (lift⊆ ζ) (suc i) = suc & eqtrenren∋ η ζ i

  -- TODO: why does rewriting blow up constraint solver here?
  module _ where
    eqtrenren : ∀ {Þ k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
                  ren (tren⊆ η ζ) (tren η d) ≡ tren η (ren ζ d)
    eqtrenren η ζ (‵var i)         = ‵var & eqtrenren∋ η ζ i
    eqtrenren η ζ (‵lam d)         = ‵lam & eqtrenren η (lift⊆ ζ) d
    eqtrenren η ζ (d ‵$ e)         = _‵$_ & eqtrenren η ζ d ⊗ eqtrenren η ζ e
    eqtrenren η ζ (‵pair d e)      = ‵pair & eqtrenren η ζ d ⊗ eqtrenren η ζ e
    eqtrenren η ζ (‵fst d)         = ‵fst & eqtrenren η ζ d
    eqtrenren η ζ (‵snd d)         = ‵snd & eqtrenren η ζ d
    eqtrenren η ζ (‵left d)        = ‵left & eqtrenren η ζ d
    eqtrenren η ζ (‵right d)       = ‵right & eqtrenren η ζ d
    eqtrenren η ζ (‵either c d e)  = ‵either
                                       & eqtrenren η ζ c
                                       ⊗ eqtrenren η (lift⊆ ζ) d
                                       ⊗ eqtrenren η (lift⊆ ζ) e

    eqtrenren {Γ = Γ} {Γ′} η ζ (‵all refl d)
        = ren (tren⊆ η ζ)
            & ( (λ ~r → ‵all ~r (tren (lift≤ η) d)) & uip _ _
              ⋮ shiftall (eqwkrenFm§ η Γ) (tren (lift≤ η) d) ⁻¹
              )
        ⋮ ‵all refl
            & ( compren (twk⊆ (tren⊆ η ζ)) (≡→⊆ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d) ⁻¹
              ⋮ (λ ~η → ren ~η (tren (lift≤ η) d)) & untitled1 η ζ ⁻¹
              ⋮ compren (≡→⊆ (eqwkrenFm§ η Γ′)) (tren⊆ (lift≤ η) (twk⊆ ζ)) (tren (lift≤ η) d)
              )
        ⋮ shiftall (eqwkrenFm§ η Γ′) (ren (tren⊆ (lift≤ η) (twk⊆ ζ)) (tren (lift≤ η) d))
        ⋮ ‵all & uip _ _ ⊗ eqtrenren (lift≤ η) (twk⊆ ζ) d

    eqtrenren η ζ (‵unall {A = A} t refl d)
        = ‵unall (renTm η t) (eqrencut0Fm η A t ⋮ refl) & eqtrenren η ζ d

    eqtrenren η ζ (‵ex {A = A} t refl d)
        = ‵ex (renTm η t) (eqrencut0Fm η A t ⋮ refl) & eqtrenren η ζ d

    eqtrenren {Γ = Γ} {Γ′} η ζ (‵letex {A = A} {C} refl refl d e)
        = ren (tren⊆ η ζ)
            & ( (λ ~r₁ ~r₂ → ‵letex ~r₁ ~r₂ (tren η d) (tren (lift≤ η) e)) & uip _ _ ⊗ uip _ _
              ⋮ shiftletex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d) (tren (lift≤ η) e) ⁻¹
              )
        ⋮ ‵letex refl (eqwkrenFm η C) (ren (tren⊆ η ζ) (tren η d))
            & ( compren (lift⊆ (twk⊆ (tren⊆ η ζ))) (lift⊆ (≡→⊆ (eqwkrenFm§ η Γ)))
                  (tren (lift≤ η) e) ⁻¹
              ⋮ (λ ~η → ren (lift⊆ ~η) (tren (lift≤ η) e)) & untitled1 η ζ ⁻¹
              ⋮ compren (lift⊆ (≡→⊆ (eqwkrenFm§ η Γ′))) (tren⊆ (lift≤ η) (lift⊆ {C = A} (twk⊆ ζ)))
                  (tren (lift≤ η) e)
              )
        ⋮ shiftletex (eqwkrenFm§ η Γ′) (eqwkrenFm η C) (ren (tren⊆ η ζ) (tren η d))
            (ren (tren⊆ (lift≤ η) (lift⊆ {C = A} (twk⊆ ζ))) (tren (lift≤ η) e))
        ⋮ ‵letex & uip _ _ ⊗ uip _ _ ⊗ eqtrenren η ζ d ⊗ eqtrenren (lift≤ η) (lift⊆ (twk⊆ ζ)) e

    eqtrenren η ζ (‵abortHA d)     = ‵abortHA & eqtrenren η ζ d
    eqtrenren η ζ (‵magicPA d)     = ‵magicPA & eqtrenren η (lift⊆ ζ) d
    eqtrenren η ζ ‵refl            = refl
    eqtrenren η ζ (‵sym d)         = ‵sym & eqtrenren η ζ d
    eqtrenren η ζ (‵trans d e)     = ‵trans & eqtrenren η ζ d ⊗ eqtrenren η ζ e

    eqtrenren η ζ (‵cong {τ = τ} {s = s} f i refl refl d)
        = ‵cong f i (eqrenpokeTm η i s τ ⋮ refl) (eqrenpeekTm η i τ ⋮ refl) & eqtrenren η ζ d

    eqtrenren η ζ ‵dis             = refl
    eqtrenren η ζ (‵inj d)         = ‵inj & eqtrenren η ζ d

    eqtrenren η ζ (‵ind {A = A} refl refl d e)
        = ‵ind (eqrencut0Fm η A 𝟘 ⋮ refl) (eqrencut1Fm η A (𝕊 (‵tvar zero)) ⋮ refl)
            & eqtrenren η ζ d
            ⊗ eqtrenren η ζ e

    eqtrenren η ζ (‵proj i refl)   = refl
    eqtrenren η ζ (‵comp g φ refl) = refl
    eqtrenren η ζ (‵rec f g)       = refl

  eqtrenren§ : ∀ {Þ k k′ Γ Γ′ Δ} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
                 ren§ (tren⊆ η ζ) (tren§ η δ) ≡ tren§ η (ren§ ζ δ)
  eqtrenren§ η ζ ∙       = refl
  eqtrenren§ η ζ (δ , d) = _,_ & eqtrenren§ η ζ δ ⊗ eqtrenren η ζ d

  eqtrenget§ : ∀ {Þ k k′ Γ Δ Δ′} (η : k ≤ k′) (ζ : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
                 get§ (tren⊆ η ζ) (tren§ η δ) ≡ tren§ η (get§ ζ δ)
  eqtrenget§ η stop      δ       = refl
  eqtrenget§ η (wk⊆ ζ)   (δ , d) = eqtrenget§ η ζ δ
  eqtrenget§ η (lift⊆ ζ) (δ , d) = (_, tren η d) & eqtrenget§ η ζ δ

  ridtren§ : ∀ {Þ k k′ Γ} (η : k ≤ k′) → tren§ {Þ = Þ} {Γ = Γ} η id§ ≡ id§
  ridtren§ {Γ = ∙}     η = refl
  ridtren§ {Γ = Γ , A} η = (_, ‵var zero)
                             & ( eqtrenren§ η (wk⊆ id⊆) id§ ⁻¹
                               ⋮ ren§ & (wk⊆ & ridtren⊆ η) ⊗ ridtren§ η
                               )


----------------------------------------------------------------------------------------------------

-- 4.11. derivations: interaction between renaming and substitution (part 1)

module _ where
  open ≡

  lidren§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → ren§ id⊆ δ ≡ δ
  lidren§ ∙       = refl
  lidren§ (δ , d) = _,_ & lidren§ δ ⊗ idren d

  compren§ : ∀ {Þ k} {Γ Γ′ Γ″ Δ : Fm§ k} (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               ren§ (η′ ∘⊆ η) δ ≡ ren§ η′ (ren§ η δ)
  compren§ η′ η ∙       = refl
  compren§ η′ η (δ , d) = _,_ & compren§ η′ η δ ⊗ compren η′ η d

  eqwkren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A C} (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
              ren (lift⊆ η) (wk {C = C} d) ≡ wk (ren η d)
  eqwkren η d = compren (lift⊆ η) (wk⊆ id⊆) d ⁻¹
              ⋮ (λ ~η → ren (wk⊆ ~η) d) & (rid⊆ η ⋮ lid⊆ η ⁻¹)
              ⋮ compren (wk⊆ id⊆) η d

  eqwkren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               ren§ (lift⊆ η) (wk§ {C = C} δ) ≡ wk§ (ren§ η δ)
  eqwkren§ η ∙       = refl
  eqwkren§ η (δ , d) = _,_ & eqwkren§ η δ ⊗ eqwkren η d

  eqliftren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
                 ren§ (lift⊆ η) (lift§ {C = C} δ) ≡ lift§ (ren§ η δ)
  eqliftren§ η δ = _,_ & eqwkren§ η δ ⊗ ridren (lift⊆ η) zero

  ridren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊆ Γ′) → ren§ {Þ = Þ} η id§ ≡ var§ η
  ridren§ stop      = refl
  ridren§ (wk⊆ η)   = (λ ~η → ren§ (wk⊆ ~η) id§) & lid⊆ η ⁻¹
                    ⋮ compren§ (wk⊆ id⊆) η id§
                    ⋮ wk§ & ridren§ η
  ridren§ (lift⊆ η) = _,_
                        & ( eqwkren§ η id§
                          ⋮ wk§ & ridren§ η
                          )
                        ⊗ ridren (lift⊆ η) zero

  eqrensub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
                sub∋ (ren§ η σ) i ≡ ren η (sub∋ σ i)
  eqrensub∋ η (σ , s) zero    = refl
  eqrensub∋ η (σ , s) (suc i) = eqrensub∋ η σ i

  eqsubren∋ : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (i : Γ ∋ A) →
                sub∋ (get§ η σ) i ≡ sub∋ σ (ren∋ η i)
  eqsubren∋ ∙       stop      i       = refl
  eqsubren∋ (σ , s) (wk⊆ η)   i       = eqsubren∋ σ η i
  eqsubren∋ (σ , s) (lift⊆ η) zero    = refl
  eqsubren∋ (σ , s) (lift⊆ η) (suc i) = eqsubren∋ σ η i

  idsub∋ : ∀ {Þ k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → sub∋ {Þ = Þ} id§ i ≡ ‵var i
  idsub∋ zero    = refl
  idsub∋ (suc i) = eqrensub∋ (wk⊆ id⊆) id§ i
                 ⋮ wk & idsub∋ i
                 ⋮ ridren (wk⊆ id⊆) i
                 ⋮ (λ ~i → ‵var (suc ~i)) & idren∋ i

  compsub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
               sub∋ (sub§ σ′ σ) i ≡ sub σ′ (sub∋ σ i)
  compsub∋ σ′ (σ , s) zero    = refl
  compsub∋ σ′ (σ , s) (suc i) = compsub∋ σ′ σ i

  idget§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → get§ id⊆ δ ≡ δ
  idget§ ∙       = refl
  idget§ (δ , d) = (_, d) & idget§ δ

  compget§ : ∀ {Þ k} {Γ Δ Δ′ Δ″ : Fm§ k} (η : Δ ⊆ Δ′) (η′ : Δ′ ⊆ Δ″) (δ : Þ / Γ ⊢§ Δ″) →
               get§ (η′ ∘⊆ η) δ ≡ get§ η (get§ η′ δ)
  compget§ η         stop       ∙       = refl
  compget§ η         (wk⊆ η′)   (δ , d) = compget§ η η′ δ
  compget§ (wk⊆ η)   (lift⊆ η′) (δ , d) = compget§ η η′ δ
  compget§ (lift⊆ η) (lift⊆ η′) (δ , d) = (_, d) & compget§ η η′ δ

  eqrenget§ : ∀ {Þ k} {Γ Γ′ Δ Δ′ : Fm§ k} (η : Γ ⊆ Γ′) (η′ : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
                get§ η′ (ren§ η δ) ≡ ren§ η (get§ η′ δ)
  eqrenget§ η stop       ∙       = refl
  eqrenget§ η (wk⊆ η′)   (δ , d) = eqrenget§ η η′ δ
  eqrenget§ η (lift⊆ η′) (δ , d) = (_, ren η d) & eqrenget§ η η′ δ

  eqwkget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               get§ (wk⊆ η) (lift§ {C = C} δ) ≡ wk§ (get§ η δ)
  eqwkget§ η δ = eqrenget§ (wk⊆ id⊆) η δ

  eqliftget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
                 get§ (lift⊆ η) (lift§ {C = C} δ) ≡ lift§ (get§ η δ)
  eqliftget§ η δ = (_, ‵var zero) & eqwkget§ η δ

  ridget§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊆ Γ′) → get§ {Þ = Þ} η id§ ≡ var§ η
  ridget§ stop      = refl
  ridget§ (wk⊆ η)   = eqrenget§ (wk⊆ id⊆) η id§
                    ⋮ wk§ & ridget§ η
  ridget§ (lift⊆ η) = (_, ‵var zero)
                        & ( eqrenget§ (wk⊆ id⊆) η id§
                          ⋮ wk§ & ridget§ η
                          )


----------------------------------------------------------------------------------------------------

-- 4.12. derivations: fundamental lemmas about substitution (part 1)

module _ where
  open ≡

  mutual
    eqrensub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
                 sub (ren§ η σ) d ≡ ren η (sub σ d)
    eqrensub η σ (‵var i)                = eqrensub∋ η σ i
    eqrensub η σ (‵lam d)                = ‵lam & eqrensublift η σ d
    eqrensub η σ (d ‵$ e)                = _‵$_ & eqrensub η σ d ⊗ eqrensub η σ e
    eqrensub η σ (‵pair d e)             = ‵pair & eqrensub η σ d ⊗ eqrensub η σ e
    eqrensub η σ (‵fst d)                = ‵fst & eqrensub η σ d
    eqrensub η σ (‵snd d)                = ‵snd & eqrensub η σ d
    eqrensub η σ (‵left d)               = ‵left & eqrensub η σ d
    eqrensub η σ (‵right d)              = ‵right & eqrensub η σ d
    eqrensub η σ (‵either c d e)         = ‵either
                                             & eqrensub η σ c
                                             ⊗ eqrensublift η σ d
                                             ⊗ eqrensublift η σ e
    eqrensub η σ (‵all refl d)           = ‵all refl
                                             & ( (λ ~σ → sub ~σ d)
                                                   & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                               ⋮ eqrensub (twk⊆ η) (twk§ σ) d
                                               )
    eqrensub η σ (‵unall t refl d)       = ‵unall t refl & eqrensub η σ d
    eqrensub η σ (‵ex t refl d)          = ‵ex t refl & eqrensub η σ d
    eqrensub η σ (‵letex refl refl d e)  = ‵letex refl refl
                                             & eqrensub η σ d
                                             ⊗ ( (λ ~σ → sub (lift§ ~σ) e)
                                                   & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                               ⋮ eqrensublift (twk⊆ η) (twk§ σ) e
                                               )
    eqrensub η σ (‵abortHA d)            = ‵abortHA & eqrensub η σ d
    eqrensub η σ (‵magicPA d)            = ‵magicPA & eqrensublift η σ d
    eqrensub η σ ‵refl                   = refl
    eqrensub η σ (‵sym d)                = ‵sym & eqrensub η σ d
    eqrensub η σ (‵trans d e)            = ‵trans & eqrensub η σ d ⊗ eqrensub η σ e
    eqrensub η σ (‵cong f i refl refl d) = ‵cong f i refl refl & eqrensub η σ d
    eqrensub η σ ‵dis                    = refl
    eqrensub η σ (‵inj d)                = ‵inj & eqrensub η σ d
    eqrensub η σ (‵ind refl refl d e)    = ‵ind refl refl & eqrensub η σ d ⊗ eqrensub η σ e
    eqrensub η σ (‵proj i refl)          = refl
    eqrensub η σ (‵comp g φ refl)        = refl
    eqrensub η σ (‵rec f g)              = refl

    eqrensublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ)
                     (d : Þ / Γ , A ⊢ B) →
                     sub (lift§ (ren§ η σ)) d ≡ ren (lift⊆ η) (sub (lift§ σ) d)
    eqrensublift η σ d = (λ ~σ → sub ~σ d) & eqliftren§ η σ ⁻¹
                       ⋮ eqrensub (lift⊆ η) (lift§ σ) d

  mutual
    eqsubren : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
                 sub (get§ η σ) d ≡ sub σ (ren η d)
    eqsubren σ η (‵var i)                = eqsubren∋ σ η i
    eqsubren σ η (‵lam d)                = ‵lam & eqsubrenlift σ η d
    eqsubren σ η (d ‵$ e)                = _‵$_ & eqsubren σ η d ⊗ eqsubren σ η e
    eqsubren σ η (‵pair d e)             = ‵pair & eqsubren σ η d ⊗ eqsubren σ η e
    eqsubren σ η (‵fst d)                = ‵fst & eqsubren σ η d
    eqsubren σ η (‵snd d)                = ‵snd & eqsubren σ η d
    eqsubren σ η (‵left d)               = ‵left & eqsubren σ η d
    eqsubren σ η (‵right d)              = ‵right & eqsubren σ η d
    eqsubren σ η (‵either c d e)         = ‵either
                                             & eqsubren σ η c
                                             ⊗ eqsubrenlift σ η d
                                             ⊗ eqsubrenlift σ η e
    eqsubren σ η (‵all refl d)           = ‵all refl
                                             & ( (λ ~σ → sub ~σ d)
                                                   & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                               ⋮ eqsubren (twk§ σ) (twk⊆ η) d
                                               )
    eqsubren σ η (‵unall t refl d)       = ‵unall t refl & eqsubren σ η d
    eqsubren σ η (‵ex t refl d)          = ‵ex t refl & eqsubren σ η d
    eqsubren σ η (‵letex refl refl d e)  = ‵letex refl refl
                                             & eqsubren σ η d
                                             ⊗ ( (λ ~σ → sub (lift§ ~σ) e)
                                                   & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                               ⋮ eqsubrenlift (twk§ σ) (twk⊆ η) e
                                               )
    eqsubren σ η (‵abortHA d)            = ‵abortHA & eqsubren σ η d
    eqsubren σ η (‵magicPA d)            = ‵magicPA & eqsubrenlift σ η d
    eqsubren σ η ‵refl                   = refl
    eqsubren σ η (‵sym d)                = ‵sym & eqsubren σ η d
    eqsubren σ η (‵trans d e)            = ‵trans & eqsubren σ η d ⊗ eqsubren σ η e
    eqsubren σ η (‵cong f i refl refl d) = ‵cong f i refl refl & eqsubren σ η d
    eqsubren σ η ‵dis                    = refl
    eqsubren σ η (‵inj d)                = ‵inj & eqsubren σ η d
    eqsubren σ η (‵ind refl refl d e)    = ‵ind refl refl & eqsubren σ η d ⊗ eqsubren σ η e
    eqsubren σ η (‵proj i refl)          = refl
    eqsubren σ η (‵comp g φ refl)        = refl
    eqsubren σ η (‵rec f g)              = refl

    eqsubrenlift : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′)
                     (d : Þ / Γ , A ⊢ B) →
                     sub (lift§ (get§ η σ)) d ≡ sub (lift§ σ) (ren (lift⊆ η) d)
    eqsubrenlift σ η d = (λ ~σ → sub ~σ d) & eqliftget§ η σ ⁻¹
                       ⋮ eqsubren (lift§ σ) (lift⊆ η) d

  idsub : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → sub id§ d ≡ d
  idsub (‵var i)                = idsub∋ i
  idsub (‵lam d)                = ‵lam & idsub d
  idsub (d ‵$ e)                = _‵$_ & idsub d ⊗ idsub e
  idsub (‵pair d e)             = ‵pair & idsub d ⊗ idsub e
  idsub (‵fst d)                = ‵fst & idsub d
  idsub (‵snd d)                = ‵snd & idsub d
  idsub (‵left d)               = ‵left & idsub d
  idsub (‵right d)              = ‵right & idsub d
  idsub (‵either c d e)         = ‵either & idsub c ⊗ idsub d ⊗ idsub e
  idsub (‵all refl d)           = ‵all refl
                                    & ( (λ ~σ → sub ~σ d)
                                          & ridtren§ (wk≤ id≤) ⋮ idsub d
                                      )
  idsub (‵unall t refl d)       = ‵unall t refl & idsub d
  idsub (‵ex t refl d)          = ‵ex t refl & idsub d
  idsub (‵letex refl refl d e)  = ‵letex refl refl
                                    & idsub d
                                    ⊗ ( (λ ~σ → sub (lift§ ~σ) e)
                                          & ridtren§ (wk≤ id≤) ⋮ idsub e
                                      )
  idsub (‵abortHA d)            = ‵abortHA & idsub d
  idsub (‵magicPA d)            = ‵magicPA & idsub d
  idsub ‵refl                   = refl
  idsub (‵sym d)                = ‵sym & idsub d
  idsub (‵trans d e)            = ‵trans & idsub d ⊗ idsub e
  idsub (‵cong f i refl refl d) = ‵cong f i refl refl & idsub d
  idsub ‵dis                    = refl
  idsub (‵inj d)                = ‵inj & idsub d
  idsub (‵ind refl refl d e)    = ‵ind refl refl & idsub d ⊗ idsub e
  idsub (‵proj i refl)          = refl
  idsub (‵comp g φ refl)        = refl
  idsub (‵rec f g)              = refl


----------------------------------------------------------------------------------------------------

-- 4.13. interaction between term renaming and derivation substitution
-- TODO: clean this up

module _ where
  open ≅

  hlidren§ : ∀ {Þ k} {Γ ^Γ Δ : Fm§ k} (p : Γ ≡ ^Γ) (δ : Þ / Γ ⊢§ Δ) → ren§ (≡→⊆ p) δ ≅ δ
  hlidren§ refl δ = ≡→≅ (lidren§ δ)

  hidget§ : ∀ {Þ k} {Γ Δ ^Δ : Fm§ k} (p : ^Δ ≡ Δ) (δ : Þ / Γ ⊢§ Δ) → get§ (≡→⊆ p) δ ≅ δ
  hidget§ refl δ = ≡→≅ (idget§ δ)

  hcomptren§ : ∀ {Þ k k′ k″ Γ Δ} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                 tren§ (η′ ∘≤ η) δ ≅ tren§ η′ (tren§ η δ)
  hcomptren§ η′ η δ = ≡→≅ (comptren§ η′ η δ)

  -- TODO: rename this
  huntitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                 ren§ (≡→⊆ (eqwkrenFm§ η Γ)) (tren§ (lift≤ η) (twk§ δ)) ≅
                   get§ (≡→⊆ (eqwkrenFm§ η Δ)) (twk§ (tren§ η δ))
  huntitled2 {Γ = Γ} {Δ} η δ = hlidren§ (eqwkrenFm§ η Γ) (tren§ (lift≤ η) (twk§ δ))
                             ⋮ hcomptren§ (lift≤ η) (wk≤ id≤) δ ⁻¹
                             ⋮ (λ ~η → tren§ (wk≤ ~η) δ) & ≡→≅ (rid≤ η ≡.⋮ lid≤ η ≡.⁻¹)
                             ⋮ hcomptren§ (wk≤ id≤) η δ
                             ⋮ hidget§ (eqwkrenFm§ η Δ) (twk§ (tren§ η δ)) ⁻¹
  -- TODO: rename this
  untitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                ren§ (≡→⊆ (eqwkrenFm§ η Γ)) (tren§ (lift≤ η) (twk§ δ)) ≡
                  get§ (≡→⊆ (eqwkrenFm§ η Δ)) (twk§ (tren§ η δ))
  untitled2 η δ = ≅→≡ (huntitled2 η δ)

module _ where
  open ≡

  eqtrensub∋ : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
                 sub∋ (tren§ η σ) (tren∋ η i) ≡ tren η (sub∋ σ i)
  eqtrensub∋ η (σ , d) zero    = refl
  eqtrensub∋ η (σ , d) (suc i) = eqtrensub∋ η σ i

  eqtrenlift§ : ∀ {Þ k k′ Γ Δ C} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                  lift§ (tren§ η δ) ≡ tren§ η (lift§ {C = C} δ)
  eqtrenlift§ η ∙       = refl
  eqtrenlift§ η (δ , d) = (_, ‵var zero)
                            & ( _,_
                                  & ( (λ ~ζ → ren§ (wk⊆ ~ζ) (tren§ η δ))
                                        & ridtren⊆ η ⁻¹
                                    )
                                  ⊗ ( (λ ~ζ → ren (wk⊆ ~ζ) (tren η d))
                                        & ridtren⊆ η ⁻¹
                                    )
                              ⋮ eqtrenren§ η (wk⊆ id⊆) (δ , d)
                              )

  -- TODO: why does rewriting blow up constraint solver here?
  module _ where
    mutual
      eqtrensub : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
                    sub (tren§ η σ) (tren η d) ≡ tren η (sub σ d)
      eqtrensub η σ (‵var i)         = eqtrensub∋ η σ i
      eqtrensub η σ (‵lam d)         = ‵lam & eqtrensublift η σ d
      eqtrensub η σ (d ‵$ e)         = _‵$_ & eqtrensub η σ d ⊗ eqtrensub η σ e
      eqtrensub η σ (‵pair d e)      = ‵pair & eqtrensub η σ d ⊗ eqtrensub η σ e
      eqtrensub η σ (‵fst d)         = ‵fst & eqtrensub η σ d
      eqtrensub η σ (‵snd d)         = ‵snd & eqtrensub η σ d
      eqtrensub η σ (‵left d)        = ‵left & eqtrensub η σ d
      eqtrensub η σ (‵right d)       = ‵right & eqtrensub η σ d
      eqtrensub η σ (‵either c d e)  = ‵either
                                         & eqtrensub η σ c
                                         ⊗ eqtrensublift η σ d
                                         ⊗ eqtrensublift η σ e

      eqtrensub {Γ = Γ} {Ξ} η σ (‵all refl d)
          = sub (tren§ η σ)
              & ( (λ ~r → ‵all ~r (tren (lift≤ η) d)) & uip (refl ⋮ eqwkrenFm§ η Γ) _
                ⋮ shiftall (eqwkrenFm§ η Γ) (tren (lift≤ η) d) ⁻¹
                )
          ⋮ ‵all refl
             & ( eqsubren (twk§ (tren§ η σ)) (≡→⊆ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d) ⁻¹
               ⋮ (λ ~σ → sub ~σ (tren (lift≤ η) d)) & untitled2 η σ ⁻¹
               ⋮ eqrensub (≡→⊆ (eqwkrenFm§ η Ξ)) (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d)
               )
          ⋮ shiftall (eqwkrenFm§ η Ξ) (sub (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d))
          ⋮ ‵all & uip _ _ ⊗ eqtrensub (lift≤ η) (twk§ σ) d

      eqtrensub η σ (‵unall {A = A} t refl d)
          = ‵unall (renTm η t) (eqrencut0Fm η A t ⋮ refl) & eqtrensub η σ d

      eqtrensub η σ (‵ex {A = A} t refl d)
          = ‵ex (renTm η t) (eqrencut0Fm η A t ⋮ refl) & eqtrensub η σ d

      eqtrensub {Γ = Γ} {Ξ} η σ (‵letex {C = C} refl refl d e)
          = sub (tren§ η σ)
              & ( (λ ~r₁ ~r₂ → ‵letex ~r₁ ~r₂ (tren η d) (tren (lift≤ η) e))
                    & uip (refl ⋮ eqwkrenFm§ η Γ) _
                    ⊗ uip _ _
                ⋮ shiftletex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d) (tren (lift≤ η) e) ⁻¹
                )
          ⋮ ‵letex refl (eqwkrenFm η C) (sub (tren§ η σ) (tren η d))
              & ( eqsubrenlift (twk§ (tren§ η σ)) (≡→⊆ (eqwkrenFm§ η Γ)) (tren (lift≤ η) e) ⁻¹
                ⋮ (λ ~σ → sub (lift§ ~σ) (tren (lift≤ η) e)) & untitled2 η σ ⁻¹
                ⋮ eqrensublift (≡→⊆ (eqwkrenFm§ η Ξ)) (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) e)
                )
          ⋮ shiftletex (eqwkrenFm§ η Ξ) (eqwkrenFm η C) (sub (tren§ η σ) (tren η d))
              (sub (lift§ (tren§ (lift≤ η) (twk§ σ))) (tren (lift≤ η) e))
          ⋮ ‵letex & uip _ _ ⊗ uip _ _ ⊗ eqtrensub η σ d ⊗ eqtrensublift (lift≤ η) (twk§ σ) e

      eqtrensub η σ (‵abortHA d)     = ‵abortHA & eqtrensub η σ d
      eqtrensub η σ (‵magicPA d)     = ‵magicPA & eqtrensublift η σ d
      eqtrensub η σ ‵refl            = refl
      eqtrensub η σ (‵sym d)         = ‵sym & eqtrensub η σ d
      eqtrensub η σ (‵trans d e)     = ‵trans & eqtrensub η σ d ⊗ eqtrensub η σ e

      eqtrensub η σ (‵cong {τ = τ} {s = s} f i refl refl d)
          = ‵cong f i (eqrenpokeTm η i s τ ⋮ refl) (eqrenpeekTm η i τ ⋮ refl) & eqtrensub η σ d

      eqtrensub η σ ‵dis             = refl
      eqtrensub η σ (‵inj d)         = ‵inj & eqtrensub η σ d

      eqtrensub η σ (‵ind {A = A} refl refl d e)
          = ‵ind (eqrencut0Fm η A 𝟘 ⋮ refl) (eqrencut1Fm η A (𝕊 (‵tvar zero)) ⋮ refl)
              & eqtrensub η σ d
              ⊗ eqtrensub η σ e

      eqtrensub η σ (‵proj i refl)   = refl
      eqtrensub η σ (‵comp g φ refl) = refl
      eqtrensub η σ (‵rec f g)       = refl

      eqtrensublift : ∀ {Þ k k′ Γ Ξ A C} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , C ⊢ A) →
                        sub (lift§ (tren§ η σ)) (tren η d) ≡ tren η (sub (lift§ σ) d)
      eqtrensublift η σ d = (λ ~σ → sub ~σ (tren η d)) & eqtrenlift§ η σ
                          ⋮ eqtrensub η (lift§ σ) d

  eqtrensub§ : ∀ {Þ k k′ Γ Ξ Δ} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
                 sub§ (tren§ η σ) (tren§ η δ) ≡ tren§ η (sub§ σ δ)
  eqtrensub§ η σ ∙       = refl
  eqtrensub§ η σ (δ , d) = _,_ & eqtrensub§ η σ δ ⊗ eqtrensub η σ d


----------------------------------------------------------------------------------------------------

-- 4.14. derivations: interaction between renaming and substitution (part 2)

module _ where
  open ≡

  eqrensub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
                sub§ (ren§ η σ) δ ≡ ren§ η (sub§ σ δ)
  eqrensub§ η σ ∙       = refl
  eqrensub§ η σ (δ , d) = _,_ & eqrensub§ η σ δ ⊗ eqrensub η σ d

  eqsubren§ : ∀ {Þ k} {Γ Γ′ Ξ Δ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
                sub§ (get§ η σ) δ ≡ sub§ σ (ren§ η δ)
  eqsubren§ σ η ∙       = refl
  eqsubren§ σ η (δ , d) = _,_ & eqsubren§ σ η δ ⊗ eqsubren σ η d

  lidsub§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → sub§ id§ δ ≡ δ
  lidsub§ ∙       = refl
  lidsub§ (δ , d) = _,_ & lidsub§ δ ⊗ idsub d

  eqsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (d : Þ / Γ ⊢ A) →
            sub (σ , s) (wk d) ≡ sub σ d
  eqsub σ s d = eqsubren (σ , s) (wk⊆ id⊆) d ⁻¹
              ⋮ (λ ~σ → sub ~σ d) & idget§ σ

  eqsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (δ : Þ / Γ ⊢§ Δ) →
             sub§ (σ , s) (wk§ δ) ≡ sub§ σ δ
  eqsub§ σ s ∙       = refl
  eqsub§ σ s (δ , d) = _,_ & eqsub§ σ s δ ⊗ eqsub σ s d

  eqwksub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A C} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
              sub (lift§ σ) (wk {C = C} d) ≡ wk (sub σ d)
  eqwksub σ d = eqsubren (lift§ σ) (wk⊆ id⊆) d ⁻¹
              ⋮ (λ ~σ → sub ~σ d)
                  & ( eqwkget§ id⊆ σ
                    ⋮ wk§ & idget§ σ
                    )
              ⋮ eqrensub (wk⊆ id⊆) σ d

  eqwksub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               sub§ (lift§ σ) (wk§ {C = C} δ) ≡ wk§ (sub§ σ δ)
  eqwksub§ σ ∙       = refl
  eqwksub§ σ (δ , d) = _,_ & eqwksub§ σ δ ⊗ eqwksub σ d

  eqliftsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
                 sub§ (lift§ σ) (lift§ {C = C} δ) ≡ lift§ (sub§ σ δ)
  eqliftsub§ σ δ = _,_ & eqwksub§ σ δ ⊗ ridsub (lift§ σ) zero

  ridsub§ : ∀ {Þ k} {Γ Ξ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ) → sub§ σ id§ ≡ σ
  ridsub§ ∙       = refl
  ridsub§ (σ , s) = _,_
                      & ( eqsub§ σ s id§
                        ⋮ ridsub§ σ
                        )
                      ⊗ ridsub (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 4.15. derivations: fundamental lemmas about substitution (part 2)

module _ where
  open ≡

  mutual
    compsub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
                sub (sub§ σ′ σ) d ≡ sub σ′ (sub σ d)

    compsub σ′ σ (‵var i)                = compsub∋ σ′ σ i
    compsub σ′ σ (‵lam d)                = ‵lam & compsublift σ′ σ d
    compsub σ′ σ (d ‵$ e)                = _‵$_ & compsub σ′ σ d ⊗ compsub σ′ σ e
    compsub σ′ σ (‵pair d e)             = ‵pair & compsub σ′ σ d ⊗ compsub σ′ σ e
    compsub σ′ σ (‵fst d)                = ‵fst & compsub σ′ σ d
    compsub σ′ σ (‵snd d)                = ‵snd & compsub σ′ σ d
    compsub σ′ σ (‵left d)               = ‵left & compsub σ′ σ d
    compsub σ′ σ (‵right d)              = ‵right & compsub σ′ σ d
    compsub σ′ σ (‵either c d e)         = ‵either
                                             & compsub σ′ σ c
                                             ⊗ compsublift σ′ σ d
                                             ⊗ compsublift σ′ σ e
    compsub σ′ σ (‵all refl d)           = ‵all refl
                                             & ( (λ ~σ → sub ~σ d)
                                                   & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                               ⋮ compsub (twk§ σ′) (twk§ σ) d
                                               )
    compsub σ′ σ (‵unall t refl d)       = ‵unall t refl & compsub σ′ σ d
    compsub σ′ σ (‵ex t refl d)          = ‵ex t refl & compsub σ′ σ d
    compsub σ′ σ (‵letex refl refl d e)  = ‵letex refl refl
                                             & compsub σ′ σ d
                                             ⊗ ( (λ ~σ → sub (lift§ ~σ) e)
                                                   & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                               ⋮ compsublift (twk§ σ′) (twk§ σ) e
                                               )
    compsub σ′ σ (‵abortHA d)            = ‵abortHA & compsub σ′ σ d
    compsub σ′ σ (‵magicPA d)            = ‵magicPA & compsublift σ′ σ d
    compsub σ′ σ ‵refl                   = refl
    compsub σ′ σ (‵sym d)                = ‵sym & compsub σ′ σ d
    compsub σ′ σ (‵trans d e)            = ‵trans & compsub σ′ σ d ⊗ compsub σ′ σ e
    compsub σ′ σ (‵cong f i refl refl d) = ‵cong f i refl refl & compsub σ′ σ d
    compsub σ′ σ ‵dis                    = refl
    compsub σ′ σ (‵inj d)                = ‵inj & compsub σ′ σ d
    compsub σ′ σ (‵ind refl refl d e)    = ‵ind refl refl & compsub σ′ σ d ⊗ compsub σ′ σ e
    compsub σ′ σ (‵proj i refl)          = refl
    compsub σ′ σ (‵comp g φ refl)        = refl
    compsub σ′ σ (‵rec f g)              = refl

    compsublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ)
                    (d : Þ / Γ , A ⊢ B) →
                    sub (lift§ (sub§ σ′ σ)) d ≡ sub (lift§ σ′) (sub (lift§ σ) d)
    compsublift σ′ σ d = (λ ~σ → sub ~σ d) & eqliftsub§ σ′ σ ⁻¹
                       ⋮ compsub (lift§ σ′) (lift§ σ) d


----------------------------------------------------------------------------------------------------

-- 4.16. derivations: interaction between renaming and substitution (part 3)

module _ where
  open ≡

  asssub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
              sub§ σ′ (sub§ σ δ) ≡ sub§ (sub§ σ′ σ) δ
  asssub§ σ′ σ ∙       = refl
  asssub§ σ′ σ (δ , d) = _,_ & asssub§ σ′ σ δ ⊗ compsub σ′ σ d ⁻¹

  eqrencut : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A B} (η : Γ ⊆ Γ′) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
               ren (lift⊆ η) d [ ren η s /0] ≡ ren η (d [ s /0])
  eqrencut η d s = eqsubren (id§ , ren η s) (lift⊆ η) d ⁻¹
                 ⋮ (λ ~σ → sub (~σ , ren η s) d) & (ridget§ η ⋮ ridren§ η ⁻¹)
                 ⋮ eqrensub η (id§ , s) d

  eqsubcut : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
               sub (lift§ σ) d [ sub σ s /0] ≡ sub σ (d [ s /0])
  eqsubcut σ d s = compsub (id§ , sub σ s) (lift§ σ) d ⁻¹
                 ⋮ (λ ~σ → sub ~σ d)
                     & ( _,_
                           & ( eqsubren§ (id§ , sub σ s) (wk⊆ id⊆) σ ⁻¹
                             ⋮ (λ ~σ → sub§ ~σ σ) & idget§ id§
                             ⋮ lidsub§ σ
                             ⋮ ridsub§ σ ⁻¹
                             )
                           ⊗ ridsub (id§ , sub σ s) zero
                       )
                 ⋮ compsub σ (id§ , s) d


----------------------------------------------------------------------------------------------------

-- 4.17. category of simultaneous substitutions of derivations

module §-Gan (funext : Funext) where
  open Gan funext
  open ⊆-Gan funext

  pshren : ∀ {Þ k} → Fm k → Presheaf (cat⊆ (Fm k)) 0ℓ
  pshren {Þ} A = record
      { ƒObj = λ Γ → Þ / Γ ⊢ A
      ; ƒ    = ren
      ; idƒ  = funext idren
      ; _∘ƒ_ = λ η′ η → funext (compren η′ η)
      }

  pshren§ : ∀ {Þ k} → Fm§ k → Presheaf (cat⊆ (Fm k)) 0ℓ
  pshren§ {Þ} Δ = record
      { ƒObj = λ Γ → Þ / Γ ⊢§ Δ
      ; ƒ    = ren§
      ; idƒ  = funext lidren§
      ; _∘ƒ_ = λ η′ η → funext (compren§ η′ η)
      }

  pshget§ : ∀ {Þ k} → Fm§ k → Presheaf (cat⊆ (Fm k) ᵒᵖ) 0ℓ
  pshget§ {Þ} Γ = record
      { ƒObj = λ Δ → Þ / Γ ⊢§ Δ
      ; ƒ    = get§
      ; idƒ  = funext idget§
      ; _∘ƒ_ = λ η′ η → funext (compget§ η′ η)
      }

  cat§ : ∀ {Þ k} → Category 0ℓ 0ℓ
  cat§ {Þ} {k} = record
      { Obj  = Fm§ k
      ; _▻_  = λ Δ Γ → Þ / Γ ⊢§ Δ -- flipped
      ; id   = id§
      ; _∘_  = sub§
      ; lid▻ = lidsub§
      ; rid▻ = ridsub§
      ; ass▻ = asssub§
      ; ◅ssa = λ τ σ σ′ → asssub§ σ′ σ τ ⁻¹
      } ᵒᵖ

  pshsub : ∀ {Þ k} → Fm k → Presheaf cat§ 0ℓ
  pshsub {Þ} A = record
      { ƒObj = λ Γ → Þ / Γ ⊢ A
      ; ƒ    = sub
      ; idƒ  = funext idsub
      ; _∘ƒ_ = λ σ′ σ → funext (compsub σ′ σ)
      }


----------------------------------------------------------------------------------------------------

-- 5.0. object-level basics

⊃id : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ A
⊃id = ‵lam 0

‵det : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ , A ⊢ B
‵det d = wk d ‵$ 0

⊃exch : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵⊃ B ‵⊃ C) ‵⊃ B ‵⊃ A ‵⊃ C
⊃exch = ‵lam (‵lam (‵lam ((2 ‵$ 0) ‵$ 1)))

‵exch : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ , B , A ⊢ C → Þ / Γ , A , B ⊢ C
‵exch d = ‵det (‵det (⊃exch ‵$ ‵lam (‵lam d)))

‵abort : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ ‵⊥ → Þ / Γ ⊢ C
‵abort {HA} d = ‵abortHA d
‵abort {PA} d = ‵magicPA (wk d)


----------------------------------------------------------------------------------------------------

-- 5.1. equational reasoning with object-level equality predicate

module _ {Þ k} {Γ : Fm§ k} where
  ≡→= : ∀ {t u} → t ≡ u → Þ / Γ ⊢ t ‵= u
  ≡→= refl = ‵refl

  module =-Reasoning where
    infix  3 _∎
    infixr 2 _=⟨⟩_ _=⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_
    infix  1 begin_

    begin_ : ∀ {t u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
    begin d = d

    _=⟨⟩_ : ∀ t {u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
    t =⟨⟩ d = d

    _=⟨_⟩_ : ∀ s {t u} → Þ / Γ ⊢ s ‵= t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
    s =⟨ d ⟩ e = ‵trans d e

    _≡⟨⟩_ : ∀ t {u} → t ≡ u → Þ / Γ ⊢ t ‵= u
    t ≡⟨⟩ p = ≡→= p

    _≡⟨_⟩_ : ∀ s {t u} → s ≡ t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
    s ≡⟨ d ⟩ e = ‵trans (≡→= d) e

    _∎ : ∀ t → Þ / Γ ⊢ t ‵= t
    t ∎ = ‵refl


----------------------------------------------------------------------------------------------------

-- 5.2. equational reasoning with object-level logical equivalence

module _ {Þ k} {Γ : Fm§ k} where
  ⫗refl : ∀ {A} → Þ / Γ ⊢ A ‵⫗ A
  ⫗refl = ‵pair ⊃id ⊃id

  ⫗sym : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ A
  ⫗sym d = ‵pair (‵snd d) (‵fst d)

  ⫗trans : ∀ {A B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  ⫗trans d e = ‵pair
                  (‵lam
                    (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ 0))
                  (‵lam
                    (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ 0))

  ‵cong⊃ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
             Þ / Γ ⊢ (A ‵⊃ B) ‵⫗ (A′ ‵⊃ B′)
  ‵cong⊃ d e = ‵pair
                 (‵lam (‵lam
                   (‵fst (wk (wk e)) ‵$ 1 ‵$ ‵snd (wk (wk d)) ‵$ 0)))
                 (‵lam (‵lam
                   (‵snd (wk (wk e)) ‵$ 1 ‵$ ‵fst (wk (wk d)) ‵$ 0)))

  ‵cong∧ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
             Þ / Γ ⊢ A ‵∧ B ‵⫗ A′ ‵∧ B′
  ‵cong∧ d e = ‵pair
                 (‵lam (‵pair
                   (‵fst (wk d) ‵$ ‵fst 0)
                   (‵fst (wk e) ‵$ ‵snd 0)))
                 (‵lam (‵pair
                   (‵snd (wk d) ‵$ ‵fst 0)
                   (‵snd (wk e) ‵$ ‵snd 0)))

  ‵cong∨ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
             Þ / Γ ⊢ A ‵∨ B ‵⫗ A′ ‵∨ B′
  ‵cong∨ d e = ‵pair
                 (‵lam (‵either 0
                   (‵left (‵fst (wk (wk d)) ‵$ 0))
                   (‵right (‵fst (wk (wk e)) ‵$ 0))))
                 (‵lam (‵either 0
                   (‵left (‵snd (wk (wk d)) ‵$ 0))
                   (‵right (‵snd (wk (wk e)) ‵$ 0))))

  -- TODO: why does rewriting blow up constraint solver here?
  module _ where
    ‵cong∀ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ ‵∀ A ‵⫗ ‵∀ A′
    ‵cong∀ {A} {A′} d = ‵pair
                          (‵lam
                            (‵all refl (ren (twk⊆ {Γ = Γ} (wk⊆ {C = ‵∀ A} id⊆)) (‵fst d) ‵$
                              ‵unall (‵tvar 0) (idcutFm A) 0)))
                          (‵lam
                            (‵all refl (ren (twk⊆ {Γ = Γ} (wk⊆ {C = ‵∀ A′} id⊆)) (‵snd d) ‵$
                              ‵unall (‵tvar 0) (idcutFm A′) 0)))

  ‵cong∃ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ ‵∃ A ‵⫗ ‵∃ A′
  ‵cong∃ {A} {A′} d = ‵pair
                        (‵lam (‵letex refl refl 0
                          (‵ex (‵tvar 0) (idcutFm A′) (‵fst (wk (wk d)) ‵$ 0))))
                        (‵lam (‵letex refl refl 0
                          (‵ex (‵tvar 0) (idcutFm A) (‵snd (wk (wk d)) ‵$ 0))))

  ≡→⫗ : ∀ {A B} → A ≡ B → Þ / Γ ⊢ A ‵⫗ B
  ≡→⫗ refl = ⫗refl

  module ⫗-Reasoning where
    infix  3 _∎
    infixr 2 _⫗⟨⟩_ _⫗⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_
    infix  1 begin_

    begin_ : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
    begin d = d

    _⫗⟨⟩_ : ∀ A {B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
    A ⫗⟨⟩ d = d

    _⫗⟨_⟩_ : ∀ A {B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
    A ⫗⟨ d ⟩ e = ⫗trans d e

    _≡⟨⟩_ : ∀ A {B} → A ≡ B → Þ / Γ ⊢ A ‵⫗ B
    A ≡⟨⟩ p = ≡→⫗ p

    _≡⟨_⟩_ : ∀ A {B C} → A ≡ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
    A ≡⟨ d ⟩ e = ⫗trans (≡→⫗ d) e

    _∎ : ∀ A → Þ / Γ ⊢ A ‵⫗ A
    A ∎ = ⫗refl


----------------------------------------------------------------------------------------------------

-- 5.3. object-level continuation/double negation monad/applicative/functor
-- ⊃-prefixed versions use object-level implication
-- ‵-prefixed versions use object-level equivalence, for use in ⫗-reasoning, or
--   meta-level implication, for general ease of use
-- TODO: laws?

⊃return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ A
⊃return = ‵lam (‵lam (0 ‵$ 1))

‵return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / Γ ⊢ ‵¬ ‵¬ A
‵return d = ⊃return ‵$ d

⊃bind : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A ‵⊃ (A ‵⊃ ‵¬ ‵¬ B) ‵⊃ ‵¬ ‵¬ B
⊃bind = ‵lam (‵lam (‵lam (2 ‵$ ‵lam ((2 ‵$ 0) ‵$ 1))))

infixl 1 _‵>>=_
_‵>>=_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ B → Þ / Γ ⊢ ‵¬ ‵¬ B
d ‵>>= e = (⊃bind ‵$ d) ‵$ e

⊃join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ A
⊃join = ‵lam (0 ‵>>= ⊃id)

‵join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ A
‵join d = ⊃join ‵$ d

⊃apply : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃apply = ‵lam (‵lam (1 ‵>>= ‵lam (1 ‵>>= ‵lam (‵return (1 ‵$ 0)))))

infixl 4 _‵⊛_
_‵⊛_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d ‵⊛ e = d ‵>>= ‵lam (wk e ‵>>= ‵lam (‵return (1 ‵$ 0)))

⊃map : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃map = ‵lam (‵lam (‵return 1 ‵⊛ 0))

infixl 4 _‵<$>_
_‵<$>_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d ‵<$> e = (⊃map ‵$ d) ‵$ e

‵dnem : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵∨ ‵¬ A)
‵dnem = ‵lam (0 ‵$ ‵right (‵lam (1 ‵$ ‵left 0)))


----------------------------------------------------------------------------------------------------

-- 5.4. object-level extended middle

⊃dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⊃ A
⊃dne = ‵lam (‵magicPA (1 ‵$ 0))

‵dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A → PA / Γ ⊢ A
‵dne d = ⊃dne ‵$ d

‵dn : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⫗ A
‵dn = ‵pair ⊃dne ⊃return

‵em : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ‵∨ ‵¬ A
‵em = ‵dne ‵dnem


----------------------------------------------------------------------------------------------------

-- 5.5. object-level de Morgan’s laws

-- constructive laws
module _ {Þ k} {Γ : Fm§ k} where
  ⊃pdm1a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⊃ ‵¬ (A ‵∨ B)
  ⊃pdm1a = ‵lam (‵lam (‵either 0
             (‵fst 2 ‵$ 0)
             (‵snd 2 ‵$ 0)))

  ⊃qdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ ‵¬ A ‵⊃ ‵¬ (‵∃ A)
  ⊃qdm1a {A} = ‵lam (‵lam (‵letex refl refl 0
                 (‵unall (‵tvar 0) (idcutFm (A ‵⊃ wkFm ‵⊥)) 2 ‵$ 0)))

  ⊃npdm1a : ∀ {A B} → Þ / Γ ⊢ A ‵∧ B ‵⊃ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  ⊃npdm1a = ‵lam (‵lam (‵abort (‵either 0
              (0 ‵$ ‵fst 2)
              (0 ‵$ ‵snd 2))))

  ⊃nqdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ A ‵⊃ ‵¬ (‵∃ ‵¬ A)
  ⊃nqdm1a {A} = ‵lam (‵lam (‵abort (‵letex refl refl 0
                  (0 ‵$ ‵unall (‵tvar 0) (idcutFm A) 2))))

  ⊃pdm2a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⊃ ‵¬ (A ‵∧ B)
  ⊃pdm2a = ‵lam (‵lam (‵either 1
             (0 ‵$ ‵fst 1)
             (0 ‵$ ‵snd 1)))

  ⊃qdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ ‵¬ A ‵⊃ ‵¬ (‵∀ A)
  ⊃qdm2a {A} = ‵lam (‵lam (‵letex refl refl 1
                 (0 ‵$ ‵unall (‵tvar 0) (idcutFm A) 1)))

  ⊃npdm2a : ∀ {A B} → Þ / Γ ⊢ A ‵∨ B ‵⊃ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  ⊃npdm2a = ‵lam (‵lam (‵abort (‵either 1
              (‵fst 1 ‵$ 0)
              (‵snd 1 ‵$ 0))))

  ⊃nqdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ A ‵⊃ ‵¬ (‵∀ ‵¬ A)
  ⊃nqdm2a {A} = ‵lam (‵lam (‵abort (‵letex refl refl 1
                  (‵unall (‵tvar 0) (idcutFm (A ‵⊃ wkFm ‵⊥)) 1 ‵$ 0))))

  ⊃pdm1b : ∀ {A B} → Þ / Γ ⊢ ‵¬ (A ‵∨ B) ‵⊃ ‵¬ A ‵∧ ‵¬ B
  ⊃pdm1b = ‵lam (‵pair
             (‵lam (1 ‵$ ‵left 0))
             (‵lam (1 ‵$ ‵right 0)))

  ⊃qdm1b : ∀ {A} → Þ / Γ ⊢ ‵¬ (‵∃ A) ‵⊃ ‵∀ ‵¬ A
  ⊃qdm1b {A} = ‵lam (‵all refl (‵lam
                 (1 ‵$ ‵ex (‵tvar 0) (idcutFm A) 0)))

  ‵pdm1 : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⫗ ‵¬ (A ‵∨ B)
  ‵pdm1 = ‵pair ⊃pdm1a ⊃pdm1b

  ‵qdm1 : ∀ {A} → Þ / Γ ⊢ ‵∀ ‵¬ A ‵⫗ ‵¬ (‵∃ A)
  ‵qdm1 = ‵pair ⊃qdm1a ⊃qdm1b

-- non-constructive laws
module _ {k} {Γ : Fm§ k} where
  ⊃npdm1b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∨ ‵¬ B) ‵⊃ A ‵∧ B
  ⊃npdm1b = ‵lam (‵pair
              (‵either ‵em
                0
                (‵abort (1 ‵$ ‵left 0)))
              (‵either ‵em
                0
                (‵abort (1 ‵$ ‵right 0))))

  ⊃nqdm1b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∃ ‵¬ A) ‵⊃ ‵∀ A
  ⊃nqdm1b {A} = ‵lam (‵all refl (‵either ‵em
                  0
                  (‵abort (1 ‵$ ‵ex (‵tvar 0) (idcutFm (A ‵⊃ ‵⊥)) 0))))

  ⊃pdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (A ‵∧ B) ‵⊃ ‵¬ A ‵∨ ‵¬ B
  ⊃pdm2b = ‵lam (‵either ‵em
             (‵either ‵em
               (‵abort (2 ‵$ ‵pair 1 0))
               (‵right 0))
             (‵left 0))

  ⊃qdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ A) ‵⊃ ‵∃ ‵¬ A
  ⊃qdm2b = ‵lam (‵either ‵em
             0
             (‵abort (1 ‵$ wk (wk ⊃nqdm1b) ‵$ 0)))

  ⊃npdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∧ ‵¬ B) ‵⊃ A ‵∨ B
  ⊃npdm2b = ‵lam (‵either ‵em
              (‵left 0)
              (‵either ‵em
                (‵right 0)
                (‵abort (2 ‵$ ‵pair 1 0))))

  ⊃nqdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ ‵¬ A) ‵⊃ ‵∃ A
  ⊃nqdm2b = ‵lam (‵either ‵em
              0
              (‵abort (1 ‵$ wk ⊃qdm1b ‵$ 0)))

  ‵npdm1 : ∀ {A B} → PA / Γ ⊢ A ‵∧ B ‵⫗ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  ‵npdm1 = ‵pair ⊃npdm1a ⊃npdm1b

  ‵nqdm1 : ∀ {A} → PA / Γ ⊢ ‵∀ A ‵⫗ ‵¬ (‵∃ ‵¬ A)
  ‵nqdm1 = ‵pair ⊃nqdm1a ⊃nqdm1b

  ‵pdm2 : ∀ {A B} → PA / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⫗ ‵¬ (A ‵∧ B)
  ‵pdm2 = ‵pair ⊃pdm2a ⊃pdm2b

  ‵qdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ ‵¬ A ‵⫗ ‵¬ (‵∀ A)
  ‵qdm2 = ‵pair ⊃qdm2a ⊃qdm2b

  ‵npdm2 : ∀ {A B} → PA / Γ ⊢ A ‵∨ B ‵⫗ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  ‵npdm2 = ‵pair ⊃npdm2a ⊃npdm2b

  ‵nqdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ A ‵⫗ ‵¬ (‵∀ ‵¬ A)
  ‵nqdm2 = ‵pair ⊃nqdm2a ⊃nqdm2b


----------------------------------------------------------------------------------------------------

-- 5.6. other object-level non-constructive tautologies
-- TODO: clean this up

{-A     B    ¬A    ¬B    A∧B   A∨B   A⊃B   A⫗B ¬A∧B  ¬A∨B  ¬A⊃B  ¬A⫗B  A∧¬B  A∨¬B  A⊃¬B A⫗¬B
----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
  0     0     1     1     0     0     1     1     0     1     0     0     0     1     1     0
  0     1     1     0     0     1     1     0     1     1     1     1     0     0     1     1
  1     0     0     1     0     1     0     0     0     0     1     1     1     1     1     1
  1     1     0     0     1     1     1     1     0     1     1     0     0     1     0     0-}

-- module _ where
--   tau1 : ∀ {A B} → PA / Γ ⊢ A ‵⊃ B ‵⫗ ‵¬ A ‵∨ B
--   tau1 = {!!}
--
--   tau2 : ∀ {A B} → PA / Γ ⊢ (‵¬ A ‵⫗ B) ‵⫗ (A ‵⫗ ‵¬ B)
--   tau2 = {!!}


----------------------------------------------------------------------------------------------------
