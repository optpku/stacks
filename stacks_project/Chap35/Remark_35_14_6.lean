module

public import ReasLib.AlgebraicGeometry.AffineSpace.SquareMap
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

variable (k : Type u) [Field k]

#check (AlgebraicGeometry.AffineSpace.squareMap k :
  𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))

#check (AlgebraicGeometry.AffineSpace.squareMap_appTop_coord k :
  (AlgebraicGeometry.AffineSpace.squareMap k).appTop
      (coord (Spec (.of k)) (ULift.up (0 : Fin 1))) =
    coord (Spec (.of k)) (ULift.up (0 : Fin 1)) ^ 2)

#check (AlgebraicGeometry.AffineSpace.squareMap_over k :
  AlgebraicGeometry.AffineSpace.squareMap k ≫
      (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) =
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))

#check (AlgebraicGeometry.AffineSpace.squareMap_surjective k :
  Surjective (AlgebraicGeometry.AffineSpace.squareMap k))

#check (AlgebraicGeometry.AffineSpace.squareMap_flat k :
  Flat (AlgebraicGeometry.AffineSpace.squareMap k))

#check (AlgebraicGeometry.AffineSpace.squareMap_locallyOfFinitePresentation k :
  LocallyOfFinitePresentation (AlgebraicGeometry.AffineSpace.squareMap k))

#check (AlgebraicGeometry.AffineSpace.smooth_over (ULift.{u} (Fin 1)) (Spec (.of k)) :
  Smooth (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))

/- Remark 35.14.6: the coordinate-squaring endomorphism of the affine line over a field
is surjective, flat, and locally of finite presentation over its smooth projection to the
base, but the endomorphism itself is not smooth. -/
@[stacks 05B6] #check (AlgebraicGeometry.AffineSpace.squareMap_not_smooth k :
  ¬ Smooth (AlgebraicGeometry.AffineSpace.squareMap k))

end AlgebraicGeometry.AffineSpace
