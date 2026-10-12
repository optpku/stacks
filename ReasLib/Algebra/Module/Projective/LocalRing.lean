/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective modules over local rings

This leaf owns the arbitrary-projective local freeness theorem. It is intentionally a named
explicit-proof theorem rather than an instance: freeness of an arbitrary projective module is a
strong result that should be requested by a proof which has established projectivity.
-/

@[expose] public section

universe u v

namespace Module.Projective

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A projective module over a local ring is free.

The projectivity hypothesis is explicit, matching the existing Module.Projective.flat API and
avoiding noncanonical local instance installation at consumers. -/
@[stacks 0593 "projective modules over local rings are free"]
theorem free_of_isLocalRing (hM : Module.Projective R M) : Module.Free R M := sorry
