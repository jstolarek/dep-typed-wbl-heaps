Dependently typed weight biased leftist heaps
=============================================

Draft version of paper "Dependently typed weight biased leftist heaps" +
companion code. This paper will be submitted to 26th International
Conference on Computer Aided Verification (CAV’14), Vienna, Austria.

## Source organization

Code is located in `src/` directory containing three subdirectories:

  * Basics - modules defining `Bool`, `Nat`, `Order`, basic functions
    for equational reasoning and proofs of elementary properties (like
    associativity and commutatibity of addition).

  * TwoPassMerge - implementation of weight biased leftist heaps based
    on a two-pass merging algorithm. Merging uses helper function
    `makeT`.

  * SinglePassMerge - implementation based on a single-pass merging
    obtained by inlining all calls to `makeT`.

## License

See LICENSE file for code license.

## Disclaimer

Everything in this repo is a work in progress.
