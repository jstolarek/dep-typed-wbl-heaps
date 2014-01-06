Verifying weight biased leftist heaps using dependent types
===========================================================

Draft version of paper "Verifying weight biased leftist heaps using
dependent types" + companion code. This paper is submitted to
[26th International Conference on Computer Aided Verification (CAV’14)]
(http://cav2014.iaik.tugraz.at/), Vienna, Austria.

## Source organization

Code is located in `src/` directory containing three subdirectories:

  * `Basics` - modules defining `Bool`, `Nat`, `Order`, basic functions
    for equational reasoning and proofs of elementary properties (like
    associativity and commutatibity of addition).

  * `TwoPassMerge` - implementation of weight biased leftist heaps based
    on a two-pass merging algorithm. Merging uses helper function
    `makeT`.

  * `SinglePassMerge` - implementation based on a single-pass merging
    obtained by inlining all calls to `makeT`.

Latest version of the source code is available [at github]
(https://github.com/jstolarek/dep-typed-wbl-heaps).

## License

See LICENSE file for code license.

## Disclaimer

Everything in this repo is a work in progress.
