module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Base change of surjective morphisms of formal algebraic spaces

Surjectivity on explicit reductions is preserved by arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- A cartesian base change of a morphism surjective on the given reductions is
surjective on the given reductions. -/
theorem Surjective.of_isPullback {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Y'] [IsFormalAlgebraicSpace B]
    (RX : ReductionData X) (RY : ReductionData Y)
    (RY' : ReductionData Y') (RB : ReductionData B)
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Surjective RY RB g) :
    Surjective RY' RX g' :=
  sorry

/-- The second pullback projection of a morphism surjective on the given
reductions is surjective on the given reductions. -/
theorem Surjective.pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] (RP : ReductionData (pullback f g))
    (hf : Surjective RX RY f) : Surjective RP RZ (pullback.snd f g) :=
  Surjective.of_isPullback RZ RX RP RY (IsPullback.of_hasPullback f g) hf

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
