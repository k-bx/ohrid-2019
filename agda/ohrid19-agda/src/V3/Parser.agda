-- FFI binding to the Haskell parser for the WHILE language.

module V3.Parser where

open import Library
open import V3.AST using (Program)

{-# FOREIGN GHC import qualified Data.Text  #-}

{-# FOREIGN GHC import While.Abs  (Program)           #-}
{-# FOREIGN GHC import While.ErrM (Err(Ok, Bad))      #-}
{-# FOREIGN GHC import While.Par  (pProgram, myLexer) #-}

-- Error monad of BNFC

data Err (A : Set) : Set where
  ok   : A → Err A
  bad  : List Char → Err A

{-# COMPILE GHC Err = data Err ( Ok | Bad ) #-}

postulate
  parse : String → Err Program

{-# COMPILE GHC parse = pProgram . myLexer . Data.Text.unpack #-}
