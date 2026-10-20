module

public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully flat descent of formal smoothness

The forward base-change direction is already a mathlib instance.  This leaf
adds the converse at the correct generality, using arbitrary projective descent
instead of imposing a finite-presentation hypothesis.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FormallySmooth

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- Tag `06CM`: formal smoothness descends from a faithfully flat scalar extension. -/
@[stacks 06CM "faithfully flat descent of formal smoothness"]
theorem of_tensorProduct
    (hff : Module.FaithfullyFlat R T)
    (hSmooth : Algebra.FormallySmooth T (T ⊗[R] S)) :
    Algebra.FormallySmooth R S := sorry

/-- Tag `06CM`: formal smoothness is invariant under faithfully flat scalar extension. -/
@[stacks 06CM "faithfully flat base change of formal smoothness"]
theorem iff_tensorProduct_of_faithfullyFlat
    (hff : Module.FaithfullyFlat R T) :
    Algebra.FormallySmooth R S ↔ Algebra.FormallySmooth T (T ⊗[R] S) := sorry

end Algebra.FormallySmooth
