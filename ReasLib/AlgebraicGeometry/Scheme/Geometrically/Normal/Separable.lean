/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Product
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyNormal

/-!
# Normality after separable field base change

Normal schemes over a field remain normal after base change along a separable
field extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A normal scheme over a field remains normal after base change along a
separable field extension. -/
@[stacks 0C3M]
theorem isNormal_baseChange_of_isSeparableOver
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableOver k K]
    (X : Over (Spec (CommRingCat.of k))) (hX : Scheme.isNormal X.left) :
    Scheme.isNormal (FieldExtension.baseChange k K X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
