module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Smooth morphisms and reductions of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The canonical reduction square of a morphism of formal algebraic spaces
that is representable by algebraic spaces and smooth is cartesian. -/
theorem ReductionData.map_isPullback_of_smooth {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y)
    (hf : AlgebraicSpace.relativeAlgebraicSpaces
      (fun {_ _} g => AlgebraicSpace.Smooth g) f) :
    IsPullback RX.ι (RX.map RY f) f RY.ι :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
