/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth

@[expose] public section

/-!
# Depth and Linear Equivalences

@stack 00LI

Module depth is invariant under a change of the module by a linear equivalence.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace LinearEquiv

/-- A linear equivalence preserves the lengths of regular sequences contained
in a fixed ideal.  This transport is independent of locality and finiteness. -/
@[stacks 00LI "regular-sequence lengths under a linear equivalence"]
theorem regularSequenceLengths_eq (e : M ≃ₗ[R] N) (I : Ideal R) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := sorry

/-- A linear equivalence preserves ideal depth for arbitrary modules. -/
@[stacks 00LI "ideal depth under a linear equivalence"]
theorem idealDepth_eq (e : M ≃ₗ[R] N) (I : Ideal R) :
    Ideal.depth I M = Ideal.depth I N := sorry

section Local

variable [IsLocalRing R]

/-- Linear equivalences preserve module depth over a local ring. -/
@[stacks 00LI "local module depth under a linear equivalence"]
theorem moduleDepth_eq (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := sorry

end Local

end LinearEquiv

section Local

variable [IsLocalRing R]

/-- Deprecated compatibility spelling for `LinearEquiv.moduleDepth_eq`. -/
@[deprecated LinearEquiv.moduleDepth_eq (since := "2026-08-04")]
theorem moduleDepth_eq_of_equiv (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := sorry

end Local
