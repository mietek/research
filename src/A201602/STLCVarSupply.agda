module A201602.STLCVarSupply where


module Stream where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (_,_; _×_)
  open import Data.Vec using (Vec; []; _∷_)

  record Stream (X : Set) : Set where
    coinductive
    field
      head : X
      tail : Stream X
  open Stream public

  take+ : {X : Set} → Stream X → X × Stream X
  take+ ∞ = head ∞ , tail ∞

  takeN+ : {X : Set} → (n : ℕ) → Stream X → Vec X n × Stream X
  takeN+ zero    ∞ = [] , ∞
  takeN+ (suc n) ∞ = let (x , ∞′) = take+ ∞
                         (xs , ∞″) = takeN+ n ∞′ in x ∷ xs , ∞″


module Var where
  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_; proj₁; _×_)
  open import Data.String using (String)
  open import Data.Vec using (Vec; []; _∷_; zipWith)
  open Stream using (Stream)

  infixr 4 _,_

  VarSupply : Set
  VarSupply = Stream ℕ

  next : VarSupply → VarSupply
  next = Stream.tail

  record Var : Set where
    constructor _,_
    field
      name   : String
      serial : ℕ
  open Var public

  make+ : String → VarSupply → Var × VarSupply
  make+ n ∞ = let s , ∞′ = Stream.take+ ∞ in (n , s) , ∞′

  make2+ : String → String → VarSupply → (Var × Var) × VarSupply
  make2+ n₁ n₂ ∞ = let v₁ , ∞′ = make+ n₁ ∞
                       v₂ , ∞″ = make+ n₂ ∞′ in (v₁ , v₂) , ∞″

  make3+ : String → String → String → VarSupply → (Var × Var × Var) × VarSupply
  make3+ n₁ n₂ n₃ ∞ = let (v₁ , v₂) , ∞′ = make2+ n₁ n₂ ∞
                          v₃ , ∞″ = make+ n₃ ∞′ in (v₁ , v₂ , v₃) , ∞″

  make4+ : String → String → String → String → VarSupply → (Var × Var × Var × Var) × VarSupply
  make4+ n₁ n₂ n₃ n₄ ∞ = let (v₁ , v₂) , ∞′ = make2+ n₁ n₂ ∞
                             (v₃ , v₄) , ∞″ = make2+ n₃ n₄ ∞′ in (v₁ , v₂ , v₃ , v₄) , ∞″

  makeN+ : ∀{n} → Vec String n → VarSupply → Vec Var n × VarSupply
  makeN+ {n} ns ∞ = let ss , ∞′ = Stream.takeN+ n ∞ in zipWith _,_ ns ss , ∞′

  make : String → VarSupply → Var
  make n ∞ = proj₁ (make+ n ∞)

  make2 : String → String → VarSupply → Var × Var
  make2 n₁ n₂ ∞ = proj₁ (make2+ n₁ n₂ ∞)

  make3 : String → String → String → VarSupply → Var × Var × Var
  make3 n₁ n₂ n₃ ∞ = proj₁ (make3+ n₁ n₂ n₃ ∞)

  make4 : String → String → String → String → VarSupply → Var × Var × Var × Var
  make4 n₁ n₂ n₃ n₄ ∞ = proj₁ (make4+ n₁ n₂ n₃ n₄ ∞)

  makeN : ∀{n} → Vec String n → VarSupply → Vec Var n
  makeN ns ∞ = proj₁ (makeN+ ns ∞)

  check : Var → VarSupply → Var
  check x ∞ = make (name x) ∞


module STLC where
  open Var using (Var; VarSupply; check; next)

  infixr 4 _,_
  infixl 3 _$_
  infixr 2 𝜆_∙_
  infixr 1 _⊃_
  infixr 0 _∣_⊢_∷_
  infixr 0 _⊩_∷_

  data Ty : Set where
    ⊥   : Ty
    _⊃_ : Ty → Ty → Ty

  data Tm : Set where
    𝑣_   : Var → Tm
    𝜆_∙_ : Var → Tm → Tm
    _$_  : Tm → Tm → Tm

  record Hyp : Set where
    constructor _,_
    field
      term : Tm
      type : Ty
  open Hyp public

  data Cx : Set where
    ∅   : Cx
    _,_ : Cx → Hyp → Cx

  data _∈_ : Hyp → Cx → Set where
    Z  : ∀{Γ h}  → h ∈ (Γ , h)
    S_ : ∀{Γ h h′}  → h ∈ Γ  → h ∈ (Γ , h′)

  data _∣_⊢_∷_ (∞ : VarSupply) (Γ : Cx) : Tm → Ty → Set where
    M𝑣_ : ∀{A t}  → (t , A) ∈ Γ
                  → ∞ ∣ Γ ⊢ t ∷ A

    M𝜆  : ∀{A B x t}  → next ∞ ∣ Γ , (𝑣 (check x ∞) , A) ⊢ t ∷ B
                      → ∞ ∣ Γ ⊢ 𝜆 x ∙ t ∷ A ⊃ B

    M∘  : ∀{A B t s}  → ∞ ∣ Γ ⊢ t ∷ A ⊃ B  → ∞ ∣ Γ ⊢ s ∷ A
                      → ∞ ∣ Γ ⊢ t $ s ∷ B

  _⊩_∷_ : VarSupply → Tm → Ty → Set
  ∞ ⊩ t ∷ A = ∀{Γ} → ∞ ∣ Γ ⊢ t ∷ A


open import Data.Product using (_,_)
open Var using (make; make2; make3)
open STLC

eI : ∀{A ∞}
   → let x = make "x" ∞ in
     ∞ ⊩ 𝜆 x ∙ 𝑣 x ∷ A ⊃ A
eI = M𝜆 (M𝑣 Z)

eK : ∀{A B ∞}
   → let x , y = make2 "x" "y" ∞ in
     ∞ ⊩ 𝜆 x ∙ 𝜆 y ∙ 𝑣 x ∷ A ⊃ B ⊃ A
eK = M𝜆 (M𝜆 (M𝑣 S Z))

eS : ∀{A B C ∞}
   → let f , g , x = make3 "f" "g" "x" ∞ in
     ∞ ⊩ 𝜆 f ∙ 𝜆 g ∙ 𝜆 x ∙ (𝑣 f $ 𝑣 x) $ (𝑣 g $ 𝑣 x) ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
eS = M𝜆 (M𝜆 (M𝜆 (M∘ (M∘ (M𝑣 S S Z)
                        (M𝑣 Z))
                    (M∘ (M𝑣 S Z)
                        (M𝑣 Z)))))
