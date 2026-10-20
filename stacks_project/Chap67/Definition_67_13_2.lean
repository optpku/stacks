module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
import StacksCheckRecall

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Definition 67.13.2: for a morphism `f : Y ⟶ X` of algebraic spaces over a scheme
`S` and a closed subspace `Z` of `X`, the inverse image `f⁻¹(Z)` is the closed
subspace `Z ×_X Y` of `Y`. -/
@[stacks 083Q] #check (AlgebraicGeometry.AlgebraicSpace.inverseImage :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i],
    AlgebraicGeometry.AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.instIsClosedImmersion_inverseImageι :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i],
    AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
      (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i))
#check (AlgebraicGeometry.AlgebraicSpace.inverseImage_spec :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i],
    (AlgebraicGeometry.AlgebraicSpace.inverseImage f i).functorOfPoints =
        CategoryTheory.Limits.pullback (C := (Over S)ᵒᵖ ⥤ Type u) f i ∧
      (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i :
        (AlgebraicGeometry.AlgebraicSpace.inverseImage f i).functorOfPoints ⟶
          Y.functorOfPoints) =
        CategoryTheory.Limits.pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f i ∧
      AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
        (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i) ∧
      CategoryTheory.IsPullback (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i)
        (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i) f i)
