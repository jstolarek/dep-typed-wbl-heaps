----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Definition of Bool datatype, which represents logical true and   --
-- false.                                                           --
----------------------------------------------------------------------

module Basics.Bool where

data Bool : Set where
  false : Bool
  true  : Bool
