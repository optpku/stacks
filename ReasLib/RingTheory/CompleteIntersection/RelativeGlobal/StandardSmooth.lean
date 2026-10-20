module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.RingHom
public import ReasLib.RingTheory.KrullDimension.StandardSmooth

@[expose] public section

/-!
# Relative Global Complete Intersections from Standard Smoothness

This leaf records the canonical implication from a submersive presentation,
and hence from standard smoothness, to a relative global complete
intersection.  The presentation-level statement is kept separate from the
intrinsic algebra and ring-hom statements so each layer can be used directly.

@stack 00T7
-/

universe u v w x

namespace Algebra

namespace SubmersivePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n c : Nat}

/-- A finite-indexed submersive presentation has the expected fiber
dimensions and is therefore a relative global complete intersection
presentation. -/
@[stacks 00T7 "submersive presentation is relative global complete intersection"]
theorem toPresentation_isRelativeGlobalCompleteIntersection
    (P : SubmersivePresentation R S (Fin n) (Fin c)) :
    Algebra.Presentation.IsRelativeGlobalCompleteIntersection P.toPresentation := sorry

/-- A submersive presentation with arbitrary finite indexing types induces the
intrinsic relative global complete intersection property after finite
reindexing. -/
@[stacks 00T7 "submersive presentation is relative global complete intersection"]
theorem isRelativeGlobalCompleteIntersection
    {ι : Type w} {σ : Type x} [Finite ι] [Finite σ]
    (P : SubmersivePresentation R S ι σ) :
    Algebra.IsRelativeGlobalCompleteIntersection R S := sorry

end SubmersivePresentation

namespace IsStandardSmooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.137.6 (5), tag `00T7`: a standard smooth `R`-algebra is a
relative global complete intersection over `R`. -/
@[stacks 00T7 "standard smooth is relative global complete intersection"]
theorem isRelativeGlobalCompleteIntersection (hS : IsStandardSmooth R S) :
    IsRelativeGlobalCompleteIntersection R S := sorry

/-- Standard smoothness supplies the canonical relative global complete
intersection instance in the forward direction. -/
@[stacks 00T7 "standard smooth is relative global complete intersection"]
instance instIsRelativeGlobalCompleteIntersection
    [IsStandardSmooth R S] : IsRelativeGlobalCompleteIntersection R S := sorry

end IsStandardSmooth

end Algebra

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace IsStandardSmooth

/-- The ring-hom form of Lemma 10.137.6 (5): a standard smooth map is a
relative global complete intersection map. -/
@[stacks 00T7 "standard smooth ring hom is relative global complete intersection"]
theorem isRelativeGlobalCompleteIntersection {f : R →+* S} (hf : f.IsStandardSmooth) :
    f.IsRelativeGlobalCompleteIntersection := sorry

end IsStandardSmooth

end RingHom
