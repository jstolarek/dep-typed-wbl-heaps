----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-heaps       --
--                                                                  --
-- Defines heap abstraction                                         --
----------------------------------------------------------------------

module Heap where

type Priority = Int

class Heap h where
    empty     :: h a
    isEmpty   :: h a -> Bool

    singleton :: Priority -> a -> h a

    merge     :: h a -> h a -> h a
    insert    :: Priority -> a -> h a -> h a

    findMin   :: h a -> a
    deleteMin :: h a -> h a
