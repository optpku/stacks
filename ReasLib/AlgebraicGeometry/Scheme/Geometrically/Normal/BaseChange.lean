module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal

/-!
# Geometric normality under field extension

This leaf records the invariance of pointwise and global geometric normality
under extension of the ground field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable (X : Over (Spec (CommRingCat.of k)))

/-- Geometric normality at a point is invariant under extension of the ground
field at any specified point of the base change lying over it. -/
@[stacks 038P]
theorem geometricallyNormalAt_iff_of_baseChange
    (x : X.left)
    (x' : (FieldExtension.Over.baseChange k k' X).left)
    (hx' : FieldExtension.Over.toSource k k' X x' = x) :
    geometricallyNormalAt X x ↔
      geometricallyNormalAt (FieldExtension.Over.baseChange k k' X) x' := sorry

/-- Geometric normality of a scheme over a field is invariant under extension
of the ground field. -/
@[stacks 038P]
theorem geometricallyNormal_iff_baseChange :
    geometricallyNormal X ↔
      geometricallyNormal (FieldExtension.Over.baseChange k k' X) := sorry

end AlgebraicGeometry.SchemeOverField
