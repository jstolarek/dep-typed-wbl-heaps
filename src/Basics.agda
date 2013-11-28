----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- This module re-exports all Basics/* modules for convenience.     --
-- Note that both Basics.Nat and Basics.Ordering define ≥ operator. --
-- Here we re-export the one from Basics.Ordering as it will be     --
-- used most of the time.                                           --
----------------------------------------------------------------------

module Basics where

open import Basics.Bool      public
open import Basics.Nat       public hiding (_≥_)
open import Basics.Ordering  public
open import Basics.Reasoning public
