/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.21.3

@stack 00EE
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.21.3: for a commutative ring `R`, every open and closed subset `U ⊆ Spec(R)` is of
the form `D(e)` for a unique idempotent `e ∈ R`. This is exactly the canonical theorem
`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`. -/
@[stacks 00EE "unique idempotent defining a clopen subset"]
#check @PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen

/- Companion recall: the induced one-to-one correspondence between idempotents of `R` and clopen
subsets of `Spec(R)` is the canonical order isomorphism
`PrimeSpectrum.isIdempotentElemEquivClopens`. -/
@[stacks 00EE "idempotents correspond to clopen subsets"]
#check @PrimeSpectrum.isIdempotentElemEquivClopens

end
