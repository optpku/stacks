module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular

/-!
# Geometric regularity under finitely generated field extension

This leaf records the invariance of pointwise and global geometric regularity
under essentially finite-type extensions of the ground field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable [Algebra.EssFiniteType k k']
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

namespace IsGeometricallyRegularAt

/-- Geometric regularity at a point is invariant under an essentially finite-type
extension of the ground field at any specified point of the base change lying over it. -/
@[stacks 038W]
theorem iff_fieldExtension (x : X) (x' : FieldExtension.baseChange k k' f)
    (hx' : FieldExtension.toSource k k' f x' = x) :
    IsGeometricallyRegularAt f x ↔
      IsGeometricallyRegularAt (FieldExtension.toBase k k' f) x' := sorry

end IsGeometricallyRegularAt

namespace IsGeometricallyRegular

/-- Geometric regularity of a scheme over a field is invariant under an essentially
finite-type extension of the ground field. -/
@[stacks 038W]
theorem iff_fieldExtension :
    IsGeometricallyRegular f ↔
      IsGeometricallyRegular (FieldExtension.toBase k k' f) := sorry

end IsGeometricallyRegular

end AlgebraicGeometry.Scheme.Hom
