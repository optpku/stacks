module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.GeometricRegularity.Smooth

/-!
# Regularity of Smooth Algebras over Regular Rings

@stack 07NF

The field case lives in `ReasLib.RingTheory.Smooth.Regularity`; this later
leaf uses geometric regularity of the fibers to ascend from an arbitrary
regular base ring.
-/

@[expose] public section

namespace Algebra.Smooth

universe u v

/-- Lemma 10.163.10, tag `07NF`: a smooth algebra over a regular ring is a regular ring. -/
@[stacks 07NF "regularity ascends along smooth algebras"]
theorem isRegularRing_of_regular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsRegularRing R] :
    IsRegularRing S := sorry

end Algebra.Smooth
