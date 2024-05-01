module A201801.STLCStandardNameResolution where

open import A201801.Prelude
open import A201801.Names
open import A201801.Fin
open import A201801.Vec
open import A201801.STLCTypes
open import A201801.STLCStandardBidirectionalTerms-CheckedInferred


--------------------------------------------------------------------------------


mutual
  data RawTermₗ : Set
    where
      LAM : Name → RawTermₗ → RawTermₗ
      INF : RawTermᵣ → RawTermₗ

  data RawTermᵣ : Set
    where
      VAR : Name → RawTermᵣ
      APP : RawTermᵣ → RawTermₗ → RawTermᵣ
      CHK : RawTermₗ → Type → RawTermᵣ


--------------------------------------------------------------------------------


mutual
  infix 3 ⊢_≫_tocheck[_]
  data ⊢_≫_tocheck[_] : ∀ {g} → RawTermₗ → Termₗ g → Names g → Set
    where
      lam : ∀ {x g P M} → {Γ : Names g}
                        → ⊢ P ≫ M tocheck[ Γ , x ]
                        → ⊢ LAM x P ≫ LAM M tocheck[ Γ ]

      inf : ∀ {g P M} → {Γ : Names g}
                      → ⊢ P ≫ M toinfer[ Γ ]
                      → ⊢ INF P ≫ INF M tocheck[ Γ ]

  infix 3 ⊢_≫_toinfer[_]
  data ⊢_≫_toinfer[_] : ∀ {g} → RawTermᵣ → Termᵣ g → Names g → Set
    where
      vz : ∀ {x g} → {Γ : Names g}
                   → ⊢ VAR x ≫ VAR zero toinfer[ Γ , x ]

      wk : ∀ {x y g I} → {Γ : Names g}
                       → x ≢ y → ⊢ VAR x ≫ VAR I toinfer[ Γ ]
                       → ⊢ VAR x ≫ VAR (suc I) toinfer[ Γ , y ]

      app : ∀ {g P Q M N} → {Γ : Names g}
                          → ⊢ P ≫ M toinfer[ Γ ] → ⊢ Q ≫ N tocheck[ Γ ]
                          → ⊢ APP P Q ≫ APP M N toinfer[ Γ ]

      chk : ∀ {A g P M} → {Γ : Names g}
                        → ⊢ P ≫ M tocheck[ Γ ]
                        → ⊢ CHK P A ≫ CHK M A toinfer[ Γ ]


--------------------------------------------------------------------------------


injvzwk : ∀ {g x y M} → {Γ : Names g}
                      → ⊢ VAR x ≫ M toinfer[ Γ , y ]
                      → x ≡ y ⊎ Σ (Termᵣ g) (\ M′ → ⊢ VAR x ≫ M′ toinfer[ Γ ])
injvzwk vz       = inj₁ refl
injvzwk (wk p 𝒟) = inj₂ (VAR _ , 𝒟)


find : ∀ {g} → (Γ : Names g) (x : Name)
             → Dec (Σ (Termᵣ g) (\ M → ⊢ VAR x ≫ M toinfer[ Γ ]))
find ∙       x  = no (\ { (M , ())})
find (Γ , y) x  with x ≟ₛ y
find (Γ , x) .x | yes refl = yes (VAR zero , vz)
find (Γ , y) x  | no x≢y   with find Γ x
find (Γ , y) x  | no x≢y   | yes (VAR I , 𝒟)    = yes (VAR (suc I) , wk x≢y 𝒟)
find (Γ , y) x  | no x≢y   | yes (APP M N , ())
find (Γ , y) x  | no x≢y   | yes (CHK M A , ())
find (Γ , y) x  | no x≢y   | no ¬M𝒟             = no (\ { (M′ , 𝒟′) → case injvzwk 𝒟′ of
                                                       (\ { (inj₁ x≡y) → x≡y ↯ x≢y
                                                          ; (inj₂ M𝒟) → M𝒟 ↯ ¬M𝒟
                                                          }) })


mutual
  resolveₗ : ∀ {g} → (Γ : Names g) (P : RawTermₗ)
                   → Dec (Σ (Termₗ g) (\ M → ⊢ P ≫ M tocheck[ Γ ]))
  resolveₗ Γ (LAM x P) with resolveₗ (Γ , x) P
  resolveₗ Γ (LAM x P) | yes (M , 𝒟) = yes (LAM M , lam 𝒟)
  resolveₗ Γ (LAM x P) | no ¬M𝒟      = no (\ { (LAM M′ , lam 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveₗ Γ (INF P)   with resolveᵣ Γ P
  resolveₗ Γ (INF P)   | yes (M , 𝒟) = yes (INF M , inf 𝒟)
  resolveₗ Γ (INF P)   | no ¬M𝒟      = no (\ { (INF M′ , inf 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })

  resolveᵣ : ∀ {g} → (Γ : Names g) (P : RawTermᵣ)
                   → Dec (Σ (Termᵣ g) (\ M → ⊢ P ≫ M toinfer[ Γ ]))
  resolveᵣ Γ (VAR x)   = find Γ x
  resolveᵣ Γ (APP P Q) with resolveᵣ Γ P | resolveₗ Γ Q
  resolveᵣ Γ (APP P Q) | yes (M , 𝒟) | yes (N , ℰ) = yes (APP M N , app 𝒟 ℰ)
  resolveᵣ Γ (APP P Q) | yes (M , 𝒟) | no ¬Nℰ      = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (N′ , ℰ′) ↯ ¬Nℰ })
  resolveᵣ Γ (APP P Q) | no ¬M𝒟      | _           = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveᵣ Γ (CHK P A) with resolveₗ Γ P
  resolveᵣ Γ (CHK P A) | yes (M , 𝒟) = yes (CHK M A , chk 𝒟)
  resolveᵣ Γ (CHK P A) | no ¬M𝒟      = no (\ { (CHK M′ A′ , chk 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })


--------------------------------------------------------------------------------
