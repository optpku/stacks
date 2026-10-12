/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Relative

@[expose] public section

/-!
@stack 00QD
# Definition 10.125.1

Both relative-dimension notions are recalled from the ReasLib owner.
-/

/-!
# Relative dimension recall

This source entry recalls the ReasLib owner.  In particular, relative dimension at a prime is
the local topological dimension of the residue-field fiber, not the Krull dimension of the fiber
local ring.
-/

universe u v

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/- Definition 10.125.1 (1), tag 00QD: the relative dimension of `S/R` at `q` is
`topologicalKrullDimAt (fiberPrimeAt R S q)`. -/
@[stacks 00QD "relative dimension at a prime"]
#check (relativeDimensionAt R S)

/- Definition 10.125.1 (2), tag 00QD: the relative dimension of `S/R` is the supremum of the
relative dimensions at target primes. -/
@[stacks 00QD "global relative dimension"]
#check (relativeDimension R S)

end
