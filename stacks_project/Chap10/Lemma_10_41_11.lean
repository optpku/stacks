/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.UniqueLiesOver
import StacksCheckRecall

/-!
# Unique primes and localizations

@stack 00EA
-/

@[expose] public section

/- Lemma 10.41.11 (1): if `q` is the unique prime of `S` lying over `p` and going up
holds for `R → S`, then `Sₚ` is also the localization of `S` at `q`. -/
@[stacks 00EA "going-up case"]
#check @IsLocalization.AtPrime.of_unique_liesOver_of_goingUp

/- Lemma 10.41.11 (2): if `q` is the unique prime of `S` lying over `p`, going down
holds for `R → S`, and every prime of `R` has at most one prime of `S` above it, then `Sₚ`
is also the localization of `S` at `q`. -/
@[stacks 00EA "going-down case"]
#check @IsLocalization.AtPrime.of_unique_liesOver_of_goingDown
