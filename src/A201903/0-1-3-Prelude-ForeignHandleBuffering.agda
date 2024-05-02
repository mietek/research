---------------------------------------------------------------------------------------------------------------
--
-- Foreign-function interface to buffering modes for I/O handles

module A201903.0-1-3-Prelude-ForeignHandleBuffering where

open import A201903.0-1-Prelude
import IO.Primitive as Prim
open import IO using (IO ; _>>_)


---------------------------------------------------------------------------------------------------------------

{-# FOREIGN GHC import qualified System.IO #-}

postulate Int : Set
{-# COMPILE GHC Int = type Int #-}

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

postulate stderr : Handle
{-# COMPILE GHC stderr = System.IO.stderr #-}

postulate hFlush : Handle → Prim.IO ⊤
{-# COMPILE GHC hFlush = System.IO.hFlush #-}


---------------------------------------------------------------------------------------------------------------

disableBuffering : IO ⊤
disableBuffering = do ♯ IO.lift (hSetBuffering stdout NoBuffering)
                      ♯ do ♯ IO.lift (hSetBuffering stderr NoBuffering)
                           ♯ do ♯ IO.lift (hFlush stdout)
                                ♯ IO.lift (hFlush stderr)


---------------------------------------------------------------------------------------------------------------
