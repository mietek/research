---------------------------------------------------------------------------------------------------------------

module Main where

open import 1-1-Syntax-Terms public
  hiding (lift)
import 4-2-1-Properties-SmallStep-NO as NO

-- TODO
open Cocolist using (Cocolist ; [] ; -∷_ ; _∷_)
import Codata.Colist as Colist
import Data.BoundedVec as BoundedVec
import Data.List as List
import Data.String as String
import Data.List.NonEmpty as List⁺
import IO.Primitive as Prim
-- open Prim
--   using ()
--   renaming (_>>=_ to _>>=′_ ; return to return′)
open import IO
  using (IO ; _>>=_ ; _>>_ ; lift ; return)
open List⁺ public
  using (List⁺ ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (inspect ; [_])


---------------------------------------------------------------------------------------------------------------

mutual
  record Machine {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    coinductive
    field
      on   : A → Results A B
      done : Results A B

  infixr 3 _▻_
  data Results {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    _▻_  : B → Results A B → Results A B
    go   : Machine A B → Results A B
    stop : Results A B

open Machine public

-- lift : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Machine A B
-- lift f .on x = f x ▻ go (lift f)
-- lift f .done = stop

_∙_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → Machine A B → Machine B C → Machine A C
(m₁ ∙ m₂) .on x = process₁ m₂ (m₁ .on x)
  where process₁ : Machine _ _ → Results _ _ → Results _ _
        process₁ m₂′ (y ▻ rs₁) = process₂ (m₂′ .on y)
          where process₂ : Results _ _ → Results _ _
                process₂ (z ▻ rs₂) = z ▻ process₂ rs₂
                process₂ (go m₂″)  = process₁ m₂″ rs₁
                process₂ stop      = process₁ m₂′ rs₁
        process₁ m₂′ (go m₁′)  = go (m₁′ ∙ m₂′)
        process₁ m₂′ stop      = stop
(m₁ ∙ m₂) .done = stop

run : ∀ {a b} {A : Set a} {B : Set b} → Machine A B → List A → List B
run m []       = process (m .done)
  where process : Results _ _ → List _
        process (y ▻ rs) = y ∷ process rs
        process (go m′)  = []
        process stop     = []
run m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → List _
        process (y ▻ rs) = y ∷ process rs
        process (go m′)  = run m′ xs
        process stop     = []

cocorun : ∀ {a b i} {A : Set a} {B : Set b} → Machine A B → Cocolist A i → Cocolist B i
cocorun         m []       = process (m .done)
  where process : Results _ _ → Cocolist _ _
        process (y ▻ rs) = y ∷ λ where .force → process rs
        process (go m′)  = []
        process stop     = []
cocorun         m (-∷ xs)  = -∷ λ where .force → cocorun m (xs .force)
cocorun {i = i} m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → Cocolist _ i
        process (y ▻ rs) = y ∷ λ where .force → process rs
        process (go m′)  = -∷ λ where .force → cocorun m′ (xs .force)
        process stop     = []

cocorerun : ∀ {a b i} {A : Set a} {B : Set b} → Machine A B → Machine A B → Colist A i → Cocolist (A ⊎ B) i
cocorerun         m₀ m []       = process (m .done)
  where process : Results _ _ → Cocolist _ _
        process (y ▻ rs) = inj₂ y ∷ λ where .force → process rs
        process (go m′)  = []
        process stop     = []
cocorerun {i = i} m₀ m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → Cocolist _ i
        process (y ▻ rs) = inj₂ y ∷ λ where .force → process rs
        process (go m′)  = -∷ λ where .force → cocorerun m₀ m′ (xs .force)
        process stop     = -∷ λ where .force → cocorerun m₀ m₀ (xs .force)

get : ∀ {a b} {A : Set a} {B : Set b} → Machine A B → List A → Maybe B
get m []       = process (m .done)
  where process : Results _ _ → Maybe _
        process (y ▻ rs) = just y
        process (go m′)  = nothing
        process stop     = nothing
get m (x ∷ xs) = process (m .on x)
  where process : Results _ _ → Maybe _
        process (y ▻ rs) = just y
        process (go m′)  = get m′ xs
        process stop     = nothing


---------------------------------------------------------------------------------------------------------------

module Chunker where
  accString : List Char → String
  accString = String.fromList ∘ List.reverse

  Acc : Set
  Acc = List Char

  mutual
    chunk : Acc → Machine Char String
    chunk a .on '\n' = go (chunkNewLine a)
    chunk a .on c    = go (chunk (c ∷ a))
    chunk a .done    = accString a ▻ stop

    chunkNewLine : Acc → Machine Char String
    chunkNewLine a .on '\n' = accString a ▻ go (chunk [])
    chunkNewLine a .on c    = go (chunk (c ∷ '\n' ∷ a))
    chunkNewLine a .done    = accString ('\n' ∷ a) ▻ stop


---------------------------------------------------------------------------------------------------------------

module Lexer where
  data Token : Set where
    beginList : Token
    endList   : Token
    atom      : String → Token

  accAtom : List Char → Token
  accAtom = atom ∘ String.fromList ∘ List.reverse

  showChar : Char → String
  showChar ' '  = "\\ "
  showChar '\t' = "\\t"
  showChar '\r' = "\\r"
  showChar '\n' = "\\n"
  showChar '('  = "\\("
  showChar ')'  = "\\)"
  showChar ';'  = "\\;"
  showChar c    = String.fromList (c ∷ [])

  showAtom : String → String
  showAtom = String.concat ∘ List.map showChar ∘ String.toList

  showToken : Token → String
  showToken beginList = "( "
  showToken endList   = ") "
  showToken (atom s)  = showAtom s ++ " "

  Acc : Set
  Acc = List Char

  mutual
    lex : Machine Char Token
    lex .on ' '  = go lex
    lex .on '\t' = go lex
    lex .on '\r' = go lex
    lex .on '\n' = go lex
    lex .on '('  = beginList ▻ go lex
    lex .on ')'  = endList ▻ go lex
    lex .on ';'  = go lexComment
    lex .on '\\' = go (lexEscape [])
    lex .on c    = go (lexAtom (c ∷ []))
    lex .done    = stop

    lexComment : Machine Char Token
    lexComment .on '\n' = go lex
    lexComment .on c    = go lexComment
    lexComment .done    = stop

    lexEscape : Acc → Machine Char Token
    lexEscape a .on ' '  = go (lexAtom (' '  ∷ a))
    lexEscape a .on 't'  = go (lexAtom ('\t' ∷ a))
    lexEscape a .on 'r'  = go (lexAtom ('\r' ∷ a))
    lexEscape a .on 'n'  = go (lexAtom ('\n' ∷ a))
    lexEscape a .on '('  = go (lexAtom ('('  ∷ a))
    lexEscape a .on ')'  = go (lexAtom (')'  ∷ a))
    lexEscape a .on ';'  = go (lexAtom (';'  ∷ a))
    lexEscape a .on '\\' = go (lexAtom ('\\' ∷ a))
    lexEscape a .on c    = go (lexAtom (c ∷ '\\' ∷ a))
    lexEscape a .done    = accAtom ('\\' ∷ a) ▻ stop

    lexAtom : Acc → Machine Char Token
    lexAtom a .on ' '  = accAtom a ▻ go lex
    lexAtom a .on '\t' = accAtom a ▻ go lex
    lexAtom a .on '\r' = accAtom a ▻ go lex
    lexAtom a .on '\n' = accAtom a ▻ go lex
    lexAtom a .on '('  = accAtom a ▻ beginList ▻ go lex
    lexAtom a .on ')'  = accAtom a ▻ endList ▻ go lex
    lexAtom a .on ';'  = accAtom a ▻ go lexComment
    lexAtom a .on '\\' = go (lexEscape a)
    lexAtom a .on c    = go (lexAtom (c ∷ a))
    lexAtom a .done    = accAtom a ▻ stop

open Lexer public
  using (Token ; beginList ; endList ; atom ; showAtom)


---------------------------------------------------------------------------------------------------------------

module GenericParser where
  data GenericTm : Set where
    atom : String → GenericTm
    list : List GenericTm → GenericTm

  accList : List GenericTm → GenericTm
  accList = list ∘ List.reverse

  mutual
    showGenericTm : GenericTm → String
    showGenericTm (atom s)  = showAtom s
    showGenericTm (list es) = showList es

    showList : List GenericTm → String
    showList es = "(" ++ showGenericTms es ++ ")"

    showGenericTms : List GenericTm → String
    showGenericTms []       = ""
    showGenericTms (e ∷ es) = showGenericTm e ++ showGenericTms′ es

    showGenericTms′ : List GenericTm → String
    showGenericTms′ []       = ""
    showGenericTms′ (e ∷ es) = " " ++ showGenericTm e ++ showGenericTms′ es

  data Error : Set where
    unexpectedEndInput : Error
    unexpectedEndList  : Error
    unexpectedInput    : Error

  showError : Error → String
  showError unexpectedEndInput = "unexpected end of input"
  showError unexpectedEndList  = "unexpected end of list"
  showError unexpectedInput    = "unexpected input"

  AccStacc : Set
  AccStacc = List⁺ (List GenericTm)

  mutual
    parse : Machine Token (Error ⊎ GenericTm)
    parse .on beginList = go (parseList ([] ∷ []))
    parse .on endList   = inj₁ unexpectedEndList ▻ stop
    parse .on (atom a)  = go (parseEndInput (atom a))
    parse .done         = stop

    parseList : AccStacc → Machine Token (Error ⊎ GenericTm)
    parseList as            .on beginList = go (parseList ([] ∷ List⁺.toList as))
    parseList (a ∷ [])      .on endList   = go (parseEndInput (accList a))
    parseList (es ∷ a ∷ as) .on endList   = go (parseList ((accList es ∷ a) ∷ as))
    parseList (a ∷ as)      .on (atom s)  = go (parseList ((atom s ∷ a) ∷ as))
    parseList as            .done         = inj₁ unexpectedEndInput ▻ stop

    parseEndInput : GenericTm → Machine Token (Error ⊎ GenericTm)
    parseEndInput e .on t = inj₁ unexpectedInput ▻ stop
    parseEndInput e .done = inj₂ e ▻ stop

  mutual
    productive-parse : ∀ (ts : List⁺ Token) → get parse (List⁺.toList ts) ≢ nothing
    productive-parse (beginList ∷ ts) = productive-parseList ts
    productive-parse (endList ∷ ts)   = λ ()
    productive-parse (atom s ∷ ts)    = productive-parseEndInput ts

    productive-parseList : ∀ {a} (ts : List Token) → get (parseList a) ts ≢ nothing
    productive-parseList               (beginList ∷ ts) = productive-parseList ts
    productive-parseList {a ∷ []}      (endList ∷ ts)   = productive-parseEndInput ts
    productive-parseList {es ∷ a ∷ as} (endList ∷ ts)   = productive-parseList ts
    productive-parseList {a ∷ as}      (atom s ∷ ts)    = productive-parseList ts
    productive-parseList               []               = λ ()

    productive-parseEndInput : ∀ {e} (ts : List Token) → get (parseEndInput e) ts ≢ nothing
    productive-parseEndInput (t ∷ ts) = λ ()
    productive-parseEndInput []       = λ ()

open GenericParser public
  using (GenericTm ; atom ; list ; showList)


---------------------------------------------------------------------------------------------------------------

module RawParser where
  data RawTm : Set where
    var : String → RawTm
    lam : String → RawTm → RawTm
    app : RawTm → RawTm → RawTm

  showRawTm : RawTm → String
  showRawTm (var s)     = "(var " ++ showAtom s ++ ")"
  showRawTm (lam s e)   = "(lam " ++ showAtom s ++ " " ++ showRawTm e ++ ")"
  showRawTm (app e₁ e₂) = "(app " ++ showRawTm e₁ ++ " " ++ showRawTm e₂ ++ ")"

  data Error : Set where
    unexpectedAtom : String → Error
    unexpectedList : List GenericTm → Error
    malformedVar   : List GenericTm → Error
    malformedLam   : List GenericTm → Error
    malformedApp   : List GenericTm → Error
    withinLam      : String → Error → Error
    withinApp₁     : Error → Error
    withinApp₂     : RawTm → Error → Error

  showError : Error → String
  showError (unexpectedAtom s)  = "unexpected atom: " ++ showAtom s
  showError (unexpectedList es) = "unexpected list: " ++ showList es
  showError (malformedVar es)   = "malformed term: " ++ showList (atom "var" ∷ es)
  showError (malformedLam es)   = "malformed term: " ++ showList (atom "lam" ∷ es)
  showError (malformedApp es)   = "malformed term: " ++ showList (atom "app" ∷ es)
  showError (withinLam s r)     = "within (lam " ++ showAtom s ++ " …):\n" ++ showError r
  showError (withinApp₁ r₁)     = "within (app … …):\n" ++ showError r₁
  showError (withinApp₂ e₁ r₂)  = "within (app " ++ showRawTm e₁ ++ " …):\n" ++ showError r₂

  mutual
    parse : GenericTm → Error ⊎ RawTm
    parse (atom s)                 = inj₁ (unexpectedAtom s)
    parse (list (atom "var" ∷ es)) = parseVar es
    parse (list (atom "lam" ∷ es)) = parseLam es
    parse (list (atom "app" ∷ es)) = parseApp es
    parse (list es)                = inj₁ (unexpectedList es)

    parseVar : List GenericTm → Error ⊎ RawTm
    parseVar (atom s ∷ []) = inj₂ (var s)
    parseVar es            = inj₁ (malformedVar es)

    parseLam : List GenericTm → Error ⊎ RawTm
    parseLam (atom s ∷ e ∷ []) with parse e
    ... | inj₁ r               = inj₁ (withinLam s r)
    ... | inj₂ e′              = inj₂ (lam s e′)
    parseLam es                = inj₁ (malformedLam es)

    parseApp : List GenericTm → Error ⊎ RawTm
    parseApp (e₁ ∷ e₂ ∷ [])   with parse e₁ | parse e₂
    ... | inj₁ r₁  | _        = inj₁ (withinApp₁ r₁)
    ... | inj₂ e₁′ | inj₁ r₂  = inj₁ (withinApp₂ e₁′ r₂)
    ... | inj₂ e₁′ | inj₂ e₂′ = inj₂ (app e₁′ e₂′)
    parseApp es               = inj₁ (malformedApp es)

open RawParser public
  using (RawTm ; var ; lam ; app ; showRawTm)


---------------------------------------------------------------------------------------------------------------

module ScopeChecker where
  toRawTm : ∀ {n} → Tm n → RawTm
  toRawTm (var s x)   = var s
  toRawTm (lam s e)   = lam s (toRawTm e)
  toRawTm (app e₁ e₂) = app (toRawTm e₁) (toRawTm e₂)

  showTm : ∀ {n} → Tm n → String
  showTm = showRawTm ∘ toRawTm

  data Error : Set where
    unboundVar : String → Error
    withinLam  : String → Error → Error
    withinApp₁ : Error → Error
    withinApp₂ : ∀ {n} → Tm n → Error → Error

  showError : Error → String
  showError (unboundVar s)     = "unbound variable: " ++ showAtom s
  showError (withinLam s r)    = "within (lam " ++ showAtom s ++ " …):\n" ++ showError r
  showError (withinApp₁ r₁)    = "within (app … …):\n" ++ showError r₁
  showError (withinApp₂ e₁ r₂) = "within (app " ++ showTm e₁ ++ " …):\n" ++ showError r₂

  findVar : ∀ {n} (ν : Vec String n) (s : String) → Maybe (∃ λ x → ν [ x ]= s)
  findVar []       s = nothing
  findVar (s′ ∷ ν) s with s ≟ s′ | findVar ν s
  ... | yes refl | _            = just (zero , here)
  ... | no s≢s′  | just (x , p) = just (suc x , there p)
  ... | no s≢s′  | nothing      = nothing

  mutual
    check : ∀ {n} → Vec String n → RawTm → Error ⊎ Tm n
    check ν (var s)     = checkVar ν s
    check ν (lam s e)   = checkLam ν s e
    check ν (app e₁ e₂) = checkApp ν e₁ e₂

    checkVar : ∀ {n} → Vec String n → String → Error ⊎ Tm n
    checkVar ν s with findVar ν s
    ... | nothing      = inj₁ (unboundVar s)
    ... | just (x , p) = inj₂ (var s x)

    checkLam : ∀ {n} → Vec String n → String → RawTm → Error ⊎ Tm n
    checkLam ν s e with check (s ∷ ν) e
    ... | inj₁ r  = inj₁ (withinLam s r)
    ... | inj₂ e′ = inj₂ (lam s e′)

    checkApp : ∀ {n} → Vec String n → RawTm → RawTm → Error ⊎ Tm n
    checkApp ν e₁ e₂ with check ν e₁ | check ν e₂
    ... | inj₁ r₁  | _        = inj₁ (withinApp₁ r₁)
    ... | inj₂ e₁′ | inj₁ r₂  = inj₁ (withinApp₂ e₁′ r₂)
    ... | inj₂ e₁′ | inj₂ e₂′ = inj₂ (app e₁′ e₂′)

open ScopeChecker public
  using (showTm)


---------------------------------------------------------------------------------------------------------------

module _ where
  postulate Int : Set
  {-# COMPILE GHC Int = type Int #-}

  {-# FOREIGN GHC import qualified System.IO #-}

  postulate Handle : Set
  {-# COMPILE GHC Handle = type System.IO.Handle #-}

  data BufferMode : Set where
    NoBuffering    : BufferMode
    LineBuffering  : BufferMode
    BlockBuffering : Maybe Int → BufferMode
  {-# COMPILE GHC BufferMode = data System.IO.BufferMode
      (System.IO.NoBuffering | System.IO.LineBuffering | System.IO.BlockBuffering)  #-}

  postulate hSetBuffering : Handle → BufferMode → Prim.IO ⊤
  {-# COMPILE GHC hSetBuffering = System.IO.hSetBuffering #-}

  postulate stdout : Handle
  {-# COMPILE GHC stdout = System.IO.stdout #-}

  postulate hFlush : Handle → Prim.IO ⊤
  {-# COMPILE GHC hFlush = System.IO.hFlush #-}


---------------------------------------------------------------------------------------------------------------

data Error : Set where
  noInput            : Error
  genericParserError : GenericParser.Error → Error
  rawParserError     : RawParser.Error → Error
  scopeCheckerError  : ScopeChecker.Error → Error

showError : Error → String
showError noInput                = "error: no input"
showError (genericParserError r) = "error: " ++ GenericParser.showError r
showError (rawParserError r)     = "error: " ++ RawParser.showError r
showError (scopeCheckerError r)  = "error: " ++ ScopeChecker.showError r

read : String → Error ⊎ Tm 0
read s                      with run Lexer.lex (String.toList s)
... | []                    = inj₁ noInput
... | t ∷ ts                with get GenericParser.parse (t ∷ ts) |
                                 inspect (get GenericParser.parse) (t ∷ ts)
... | nothing       | [ q ] = q ↯ GenericParser.productive-parse (t ∷ ts)
... | just (inj₁ r) | _     = inj₁ (genericParserError r)
... | just (inj₂ e) | _     with RawParser.parse e
... | inj₁ r                = inj₁ (rawParserError r)
... | inj₂ e′               with ScopeChecker.check [] e′
... | inj₁ r                = inj₁ (scopeCheckerError r)
... | inj₂ e″               = inj₂ e″

fromColist : ∀ {a} {A : Set a} → Nat → Colist A ∞ → List A
fromColist n xs = BoundedVec.toList (Colist.take n xs)

eval : Error ⊎ Tm 0 → Error ⊎ List (Tm 0)
eval (inj₁ r) = inj₁ r
eval (inj₂ e) = inj₂ (fromColist 100 (NO.trace (NO.eval e))) -- TODO: allow resuming

print : Error ⊎ List (Tm 0) → String
print (inj₁ r)        = showError r ++ "\n\n"
print (inj₂ [])       = "\n\n"
print (inj₂ (e ∷ es)) = showTm e ++ "\n" ++ print (inj₂ es)

Acc : Set
Acc = List Char

accString : List Char → String
accString = String.fromList ∘ List.reverse

fromColist′ : ∀ {a} {A : Set a} → Nat → Colist A ∞ → List A × Colist A ∞
fromColist′ zero    xs       = [] , xs
fromColist′ (suc n) []       = [] , []
fromColist′ (suc n) (x ∷ xs) with fromColist′ n (xs .force)
... | xs′ , xs″              = x ∷ xs′ , xs″


mutual
  loop : Acc → Machine Char String
  loop a .on '\n' = go (loopNewline a)
  loop a .on c    = go (loop (c ∷ a))
  loop a .done    = "\nstopped\n" ▻ stop

  loopNewline : Acc → Machine Char String
  loopNewline a .on '\n' with read (accString a)
  ... | inj₁ r           = showError r ++ "\n> " ▻ go (loop [])
  ... | inj₂ e           = process (fromColist′ 10 (NO.trace (NO.eval e)))
    where process : ∀ {n} → List (Tm n) × Colist (Tm n) ∞ → Results Char String
          process ((e ∷ es) , es′) = showTm e ++ "\n" ▻ process (es , es′)
          process ([]       , [])  = "\n> " ▻ go (loop [])
          process ([]       , es′) = "continue? (y/n) > " ▻ go (loopContinueEval es′)
  loopNewline a .on c    = go (loop (c ∷ '\n' ∷ a))
  loopNewline a .done    = "\nstopped\n" ▻ stop

  loopContinueEval : ∀ {n} → Colist (Tm n) ∞ → Machine Char String
  loopContinueEval es .on 'y' = process (fromColist′ 10 es)
    where process : ∀ {n} → List (Tm n) × Colist (Tm n) ∞ → Results Char String
          process ((e ∷ es) , es′) = showTm e ++ "\n" ▻ process (es , es′)
          process ([] , [])        = "\n> " ▻ go (loop [])
          process ([] , es′)       = "continue? (y/n) > " ▻ go (loopContinueEval es′)
  loopContinueEval es .on 'n'  = "\n> " ▻ go (loop [])
  loopContinueEval es .on ' '  = go (loopContinueEval es)
  loopContinueEval es .on '\t' = go (loopContinueEval es)
  loopContinueEval es .on '\r' = go (loopContinueEval es)
  loopContinueEval es .on '\n' = go (loopContinueEval es)
  loopContinueEval es .on c    = "continue? (y/n) > " ▻ go (loopContinueEval es)
  loopContinueEval es .done    = "\nstopped\n" ▻ stop


main : Prim.IO (Lift 0ᴸ ⊤)
main = IO.run do ♯ lift (hSetBuffering stdout NoBuffering)
                 ♯ do ♯ IO.putStr "> "
                      ♯ do s ← ♯ IO.getContents
                           let ss = cocorun (loop []) (Cocolist.fromCostring s)
                           ♯ Cocolist.mapM′ IO.putStr ss


---------------------------------------------------------------------------------------------------------------
