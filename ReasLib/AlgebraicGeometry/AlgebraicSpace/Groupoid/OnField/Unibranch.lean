module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch

/-!
# Geometric unibranchness of groupoids on fields

The arrow algebraic space of a groupoid on a field is geometrically unibranch.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The arrow algebraic space of a groupoid whose object space is the spectrum of a field
is geometrically unibranch. -/
theorem isGeometricallyUnibranch {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.IsGeometricallyUnibranch G.R.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
