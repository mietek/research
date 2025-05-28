{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------

module A201903.Main where

import A201903.0-1-1-Prelude-StutteringColists as Cocolist
open import A201903.0-1-2-Prelude-MealyLikeMachines as Machine
import A201903.0-1-3-Prelude-ForeignHandleBuffering as Foreign
open import A201903.1-1-Syntax-Terms
import A201903.4-2-Properties-SmallStep-NO as NO
import Data.List as List
import Data.String as String
import Data.List.NonEmpty as List⁺
import IO.Primitive.Core as Prim
open import IO using (IO) renaming (bind to _>>=_)


---------------------------------------------------------------------------------------------------------------
--
-- Lexer for S-expressions, with C-like escape sequences

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

open Lexer using (Token ; beginList ; endList ; atom ; showAtom ; showToken)


---------------------------------------------------------------------------------------------------------------
--
-- Parser for generic terms, or S-expressions

module GenParser where
  data GenTm : Set where
    atom : String → GenTm
    list : List GenTm → GenTm

  accList : List GenTm → GenTm
  accList = list ∘ List.reverse

  mutual
    showGenTm : GenTm → String
    showGenTm (atom s)  = showAtom s
    showGenTm (list es) = "(" ++ showGenTms es ++ ")"

    showGenTms : List GenTm → String
    showGenTms []       = ""
    showGenTms (e ∷ es) = showGenTm e ++ showGenTms′ es

    showGenTms′ : List GenTm → String
    showGenTms′ []       = ""
    showGenTms′ (e ∷ es) = " " ++ showGenTm e ++ showGenTms′ es

  data Error : Set where
    unexpectedEndInput : Error
    unexpectedEndList  : Error
    unexpectedInput    : GenTm → Token → Error

  showError : Error → String
  showError unexpectedEndInput    = "unexpected end of input"
  showError unexpectedEndList     = "unexpected end of list"
  showError (unexpectedInput e t) = "after " ++ showGenTm e ++ ":\n  " ++
                                    "unexpected input: " ++ showToken t

  AccStacc : Set
  AccStacc = List⁺ (List GenTm)

  mutual
    parse : Machine Token (Error ⊎ GenTm)
    parse .on beginList = go (parseList ([] ∷ []))
    parse .on endList   = inj₁ unexpectedEndList ▻ stop
    parse .on (atom a)  = go (parseEndInput (atom a))
    parse .done         = stop

    parseList : AccStacc → Machine Token (Error ⊎ GenTm)
    parseList as            .on beginList = go (parseList ([] ∷ List⁺.toList as))
    parseList (a ∷ [])      .on endList   = go (parseEndInput (accList a))
    parseList (es ∷ a ∷ as) .on endList   = go (parseList ((accList es ∷ a) ∷ as))
    parseList (a ∷ as)      .on (atom s)  = go (parseList ((atom s ∷ a) ∷ as))
    parseList as            .done         = inj₁ unexpectedEndInput ▻ stop

    parseEndInput : GenTm → Machine Token (Error ⊎ GenTm)
    parseEndInput e .on t = inj₁ (unexpectedInput e t) ▻ stop
    parseEndInput e .done = inj₂ e ▻ stop

  mutual
    productive-runOnce-parse : ∀ (ts : List Token) → ts ≢ [] → runOnce parse ts ≢ nothing
    productive-runOnce-parse (beginList ∷ ts) q = productive-runOnce-parseList ts
    productive-runOnce-parse (endList ∷ ts)   q = λ ()
    productive-runOnce-parse (atom s ∷ ts)    q = productive-runOnce-parseEndInput ts
    productive-runOnce-parse []               q = refl ↯ q

    productive-runOnce-parseList : ∀ {a} (ts : List Token) → runOnce (parseList a) ts ≢ nothing
    productive-runOnce-parseList               (beginList ∷ ts) = productive-runOnce-parseList ts
    productive-runOnce-parseList {a ∷ []}      (endList ∷ ts)   = productive-runOnce-parseEndInput ts
    productive-runOnce-parseList {es ∷ a ∷ as} (endList ∷ ts)   = productive-runOnce-parseList ts
    productive-runOnce-parseList {a ∷ as}      (atom s ∷ ts)    = productive-runOnce-parseList ts
    productive-runOnce-parseList               []               = λ ()

    productive-runOnce-parseEndInput : ∀ {e} (ts : List Token) → runOnce (parseEndInput e) ts ≢ nothing
    productive-runOnce-parseEndInput (t ∷ ts) = λ ()
    productive-runOnce-parseEndInput []       = λ ()

open GenParser using (GenTm ; atom ; list ; showGenTm)


---------------------------------------------------------------------------------------------------------------
--
-- Parser for raw terms, or non-well-scoped λ-calculus terms, with names

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
    unexpectedList : List GenTm → Error
    malformedVar   : List GenTm → Error
    malformedLam   : List GenTm → Error
    malformedApp   : List GenTm → Error
    withinLam      : String → Error → Error
    withinApp₁     : Error → Error
    withinApp₂     : RawTm → Error → Error

  showError : Error → String
  showError (unexpectedAtom s)  = "unexpected atom: " ++ showGenTm (atom s)
  showError (unexpectedList es) = "unexpected list: " ++ showGenTm (list es)
  showError (malformedVar es)   = "malformed term: " ++ showGenTm (list (atom "var" ∷ es))
  showError (malformedLam es)   = "malformed term: " ++ showGenTm (list (atom "lam" ∷ es))
  showError (malformedApp es)   = "malformed term: " ++ showGenTm (list (atom "app" ∷ es))
  showError (withinLam s r)     = "within (lam " ++ showAtom s ++ " #):\n  " ++ showError r
  showError (withinApp₁ r₁)     = "within (app # …):\n  " ++ showError r₁
  showError (withinApp₂ e₁ r₂)  = "within (app " ++ showRawTm e₁ ++ " #):\n  " ++ showError r₂

  mutual
    parse : GenTm → Error ⊎ RawTm
    parse (atom s)                 = inj₁ (unexpectedAtom s)
    parse (list (atom "var" ∷ es)) = parseVar es
    parse (list (atom "lam" ∷ es)) = parseLam es
    parse (list (atom "app" ∷ es)) = parseApp es
    parse (list es)                = inj₁ (unexpectedList es)

    parseVar : List GenTm → Error ⊎ RawTm
    parseVar (atom s ∷ []) = inj₂ (var s)
    parseVar es            = inj₁ (malformedVar es)

    parseLam : List GenTm → Error ⊎ RawTm
    parseLam (atom s ∷ e ∷ []) with parse e
    ... | inj₁ r               = inj₁ (withinLam s r)
    ... | inj₂ e′              = inj₂ (lam s e′)
    parseLam es                = inj₁ (malformedLam es)

    parseApp : List GenTm → Error ⊎ RawTm
    parseApp (e₁ ∷ e₂ ∷ [])   with parse e₁ | parse e₂
    ... | inj₁ r₁  | _        = inj₁ (withinApp₁ r₁)
    ... | inj₂ e₁′ | inj₁ r₂  = inj₁ (withinApp₂ e₁′ r₂)
    ... | inj₂ e₁′ | inj₂ e₂′ = inj₂ (app e₁′ e₂′)
    parseApp es               = inj₁ (malformedApp es)

open RawParser using (RawTm ; var ; lam ; app ; showRawTm)


---------------------------------------------------------------------------------------------------------------
--
-- Scope checker for λ-calculus terms

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
  showError (withinLam s r)    = "within (lam " ++ showAtom s ++ " #):\n  " ++ showError r
  showError (withinApp₁ r₁)    = "within (app # …):\n  " ++ showError r₁
  showError (withinApp₂ e₁ r₂) = "within (app " ++ showTm e₁ ++ " #):\n  " ++ showError r₂

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

open ScopeChecker using (showTm)


---------------------------------------------------------------------------------------------------------------
--
-- Coinductive read/eval/show loop

module RESL where
  data Error : Set where
    noInput           : Error
    genParserError    : GenParser.Error → Error
    rawParserError    : RawParser.Error → Error
    scopeCheckerError : ScopeChecker.Error → Error

  showError : Error → String
  showError noInput               = "no input"
  showError (genParserError r)    = GenParser.showError r
  showError (rawParserError r)    = RawParser.showError r
  showError (scopeCheckerError r) = ScopeChecker.showError r

  data Action : Set where
    echoNewline  : Action
    echoPrompt   : Action
    echoTm       : ∀ {n} → Tm n → Action
    echoError    : Error → Action
    echoContinue : Action
    echoGoodbye  : Action

  showAction : Action → String
  showAction echoNewline   = "\n"
  showAction echoPrompt    = "\n> "
  showAction (echoTm e)    = showTm e ++ "\n"
  showAction (echoError r) = "error: " ++ showError r ++ "\n\n"
  showAction echoContinue  = "continue? (y/n) > "
  showAction echoGoodbye   = "\ngoodbye\n"

  evalLimit : Nat
  evalLimit = 10

  read : String → Error ⊎ Tm 0
  read s                    with run Lexer.lex (String.toList s)
  ... | []                  = inj₁ noInput
  ... | ts@(_ ∷ _)          with runOnce GenParser.parse ts | inspect (runOnce GenParser.parse) ts
  ... | nothing       | q ⁱ = q ↯ GenParser.productive-runOnce-parse ts λ ()
  ... | just (inj₁ r) | _   = inj₁ (genParserError r)
  ... | just (inj₂ e) | _   with RawParser.parse e
  ... | inj₁ r              = inj₁ (rawParserError r)
  ... | inj₂ e′             with ScopeChecker.check [] e′
  ... | inj₁ r              = inj₁ (scopeCheckerError r)
  ... | inj₂ e″             = inj₂ e″

  eval : ∀ {n} → Tm n → Colist (Tm n) ∞
  eval = NO.trace ∘ NO.eval

  accString : List Char → String
  accString = String.fromList ∘ List.reverse

  Acc : Set
  Acc = List Char

  mutual
    loop : Acc → Machine Char Action
    loop a .on '\n' = go (loopNewline a)
    loop a .on c    = go (loop (c ∷ a))
    loop a .done    = echoGoodbye ▻ stop

    loopNewline : Acc → Machine Char Action
    loopNewline a .on '\n' with read (accString a)
    ... | inj₁ r           = echoError r ▻ echoPrompt ▻ go (loop [])
    ... | inj₂ e           = process (splitAt evalLimit (eval e))
    loopNewline a .on c    = go (loop (c ∷ '\n' ∷ a))
    loopNewline a .done    = echoGoodbye ▻ stop

    loopContinueEval : ∀ {n} → Colist (Tm n) ∞ → Machine Char Action
    loopContinueEval es .on 'y'  = process (splitAt evalLimit es)
    loopContinueEval es .on 'n'  = echoNewline ▻ echoPrompt ▻ go (loop [])
    loopContinueEval es .on ' '  = go (loopContinueEval es)
    loopContinueEval es .on '\t' = go (loopContinueEval es)
    loopContinueEval es .on '\r' = go (loopContinueEval es)
    loopContinueEval es .on '\n' = go (loopContinueEval es)
    loopContinueEval es .on c    = echoContinue ▻ go (loopContinueEval es)
    loopContinueEval es .done    = echoGoodbye ▻ stop

    process : ∀ {n} → List (Tm n) × Colist (Tm n) ∞ → Results Char Action
    process ((e ∷ es) , es′) = echoTm e ▻ process (es , es′)
    process ([] , [])        = echoNewline ▻ echoPrompt ▻ go (loop [])
    process ([] , es′)       = echoContinue ▻ go (loopContinueEval es′)


---------------------------------------------------------------------------------------------------------------
--
-- I/O handling

main : Prim.IO (Lift 0ᴸ ⊤)
main = IO.run do _ ← ♯ Foreign.disableBuffering
                 ♯ do _ ← ♯ IO.putStr "> "
                      ♯ do s ← ♯ IO.getContents
                           let ss = cocorun (RESL.loop []) (Cocolist.fromCostring s)
                           ♯ Cocolist.mapM′ (IO.putStr ∘ RESL.showAction) ss


---------------------------------------------------------------------------------------------------------------
