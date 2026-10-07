module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.OverField
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.StandardSmooth

@[expose] public section

/-!
# Smooth Algebras over a Field as Local Complete Intersections

This leaf records the intrinsic consequence of smoothness over a field.  The
standard-smooth cover and the relative-global complete-intersection bridges
remain owned by their respective layers.
-/

universe u v

namespace Algebra

namespace Smooth

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Lemma 10.137.4, tag `00T5`: every smooth algebra over a field is a local
complete intersection. -/
@[stacks 00T5 "smooth algebra over a field is local complete intersection"]
theorem isLocalCompleteIntersection (hS : Smooth k S) :
    IsLocalCompleteIntersection k S := sorry

/-- Smoothness over a field supplies the canonical local complete-intersection
instance. -/
@[stacks 00T5 "smooth algebra over a field is local complete intersection"]
instance instIsLocalCompleteIntersection [Smooth k S] :
    IsLocalCompleteIntersection k S := sorry

end Smooth

end Algebra
