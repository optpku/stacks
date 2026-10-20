module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

/-!
# Geometric reducedness under field extension

This file records pointwise and global invariance of geometric reducedness
under extension of the ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable (X : Over (Spec (CommRingCat.of k)))

namespace geometricallyReducedAt

/-- Geometric reducedness at a point is invariant under field extension at
any point of the base change lying over the original point. -/
theorem iff_baseChange
    (x : X.left) (x' : (FieldExtension.Over.baseChange k k' X).left)
    (hx' : FieldExtension.Over.toSource k k' X x' = x) :
    geometricallyReducedAt X x ↔
      geometricallyReducedAt (FieldExtension.Over.baseChange k k' X) x' := sorry

end geometricallyReducedAt

namespace geometricallyReduced

/-- Geometric reducedness of a scheme is invariant under extension of the
ground field. -/
theorem iff_baseChange :
    geometricallyReduced X ↔
      geometricallyReduced (FieldExtension.Over.baseChange k k' X) := sorry

end geometricallyReduced

end AlgebraicGeometry.SchemeOverField
