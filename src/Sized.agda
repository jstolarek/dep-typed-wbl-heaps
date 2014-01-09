-- This module is copied from Agda's standard library. It has been
-- renamed (original name is Size) to avoid name clash in case you
-- have the standard library installed.

------------------------------------------------------------------------
-- The Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Sized where

postulate
  Size : Set
  ↑_   : Size → Size
  ∞    : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ↑_   #-}
{-# BUILTIN SIZEINF ∞    #-}
