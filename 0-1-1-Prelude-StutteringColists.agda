---------------------------------------------------------------------------------------------------------------
--
-- Stuttering colists

module 0-1-1-Prelude-StutteringColists where

open import 0-1-Prelude
import Codata.Musical.Colist as Colist
import Data.String as String
open import IO using (IO ; _>>=_ ; _>>_ ; return)


---------------------------------------------------------------------------------------------------------------

data Cocolist {a} (A : Set a) (i : Size) : Set a where
  []  : Cocolist A i
  -∷_ : Thunk (Cocolist A) i → Cocolist A i
  _∷_ : A → Thunk (Cocolist A) i → Cocolist A i

fromColist : ∀ {a i} {A : Set a} → Colist A i → Cocolist A i
fromColist []       = []
fromColist (x ∷ xs) = x ∷ λ where .force → fromColist (xs .force)

fromCostring : Costring → Cocolist Char ∞
fromCostring = fromColist ∘ Colist.fromMusical

fromList : ∀ {a} {A : Set a} → List A → Cocolist A ∞
fromList []       = []
fromList (x ∷ xs) = x ∷ λ where .force → fromList xs

fromString : String → Cocolist Char ∞
fromString = fromList ∘ String.toList

toList : ∀ {a} {A : Set a} → Nat → Cocolist A ∞ → List A
toList zero    xs       = []
toList (suc n) []       = []
toList (suc n) (-∷ xs)  = toList n (xs .force)
toList (suc n) (x ∷ xs) = x ∷ toList n (xs .force)

map : ∀ {a b i} {A : Set a} {B : Set b} (f : A → B) → Cocolist A i → Cocolist B i
map f []       = []
map f (-∷ xs)  = -∷ λ where .force → map f (xs .force)
map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)

sequence : ∀ {a} {A : Set a} → Cocolist (IO A) ∞ → IO (Cocolist A ∞)
sequence []       = return []
sequence (-∷ as)  = do xs ← ♯ sequence (as .force)
                       ♯ return xs
sequence (a ∷ as) = do x ← ♯ a
                       ♯ (do xs ← ♯ sequence (as .force)
                             ♯ return (x ∷ λ where .force → xs))

sequence′ : ∀ {a} {A : Set a} → Cocolist (IO A) ∞ → IO (Lift a ⊤)
sequence′ []       = return _
sequence′ (-∷ as)  = do ♯ sequence (as .force)
                        ♯ return _
sequence′ (a ∷ as) = do ♯ a
                        ♯ (do ♯ sequence′ (as .force)
                              ♯ return _)

mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → Cocolist A ∞ → IO (Cocolist B ∞)
mapM f = sequence ∘ map f

mapM′ : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → Cocolist A ∞ → IO (Lift b ⊤)
mapM′ f = sequence′ ∘ map f


---------------------------------------------------------------------------------------------------------------
