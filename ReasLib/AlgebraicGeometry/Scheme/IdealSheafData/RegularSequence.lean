module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import Mathlib.RingTheory.Regular.RegularSequence

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- An ideal sheaf is generated at `x` by a regular sequence of exactly `r` elements. -/
def IsGeneratedByRegularSequenceAt (Z : X.IdealSheafData) (x : X) (r : ℕ) : Prop :=
  ∃ a : Fin r → X.presheaf.stalk x,
    RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (List.ofFn a) ∧
      RingedSpace.idealSheafStalkIdeal Z.toSubobject x = Ideal.span (Set.range a)

/-- Fixed-length regular generation is equivalent to the existence of `r` stalk elements forming
a regular sequence and spanning the stalk ideal. -/
theorem isGeneratedByRegularSequenceAt_iff (Z : X.IdealSheafData) (x : X) (r : ℕ) :
    Z.IsGeneratedByRegularSequenceAt x r ↔
      ∃ a : Fin r → X.presheaf.stalk x,
        RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (List.ofFn a) ∧
          RingedSpace.idealSheafStalkIdeal Z.toSubobject x = Ideal.span (Set.range a) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
