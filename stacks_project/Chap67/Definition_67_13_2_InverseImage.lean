/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Inverse images of closed subspaces of algebraic spaces

The inverse image of a closed subspace `Z` of an algebraic space `X` along a
morphism `f : Y ⟶ X` is the fibre product `Z ×_X Y`, viewed as a closed subspace
of `Y`. The fibre product is formed in the functor-of-points category.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces, as a natural transformation of functors of points. -/
def toFunctorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  f

/-- `toFunctorOfPoints f` is the underlying natural transformation of `f`. -/
theorem toFunctorOfPoints_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    toFunctorOfPoints f = f :=
  rfl

#check (AlgebraicGeometry.AlgebraicSpace.inverseImage_spec :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i],
    (AlgebraicGeometry.AlgebraicSpace.inverseImage f i).functorOfPoints =
        CategoryTheory.Limits.pullback (C := (Over S)ᵒᵖ ⥤ Type u) f i ∧
      (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i :
        (AlgebraicGeometry.AlgebraicSpace.inverseImage f i).functorOfPoints ⟶
          Y.functorOfPoints) =
        CategoryTheory.Limits.pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f i ∧
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
        (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i) ∧
      IsPullback (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i)
        (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i) f i)

end AlgebraicGeometry.AlgebraicSpace
