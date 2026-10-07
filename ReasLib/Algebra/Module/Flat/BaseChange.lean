module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness under scalar extension of a module

This module records preservation of flatness under scalar extension along flat maps and
detection of flatness after scalar extension along faithfully flat maps.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/-- Scalar extension along a flat map preserves flatness over the original base ring. -/
@[stacks 0584 "flat base change"]
theorem baseChange_of_flat [Module.Flat S S'] [Module.Flat R M] :
    Module.Flat R (S' ⊗[S] M) := sorry

/-- Scalar extension along a faithfully flat map detects and preserves flatness over the
original base ring. -/
@[stacks 0584 "faithfully flat base change"]
theorem iff_baseChange_of_faithfullyFlat [Module.FaithfullyFlat S S'] :
    Module.Flat R M ↔ Module.Flat R (S' ⊗[S] M) := sorry

end Module.Flat
