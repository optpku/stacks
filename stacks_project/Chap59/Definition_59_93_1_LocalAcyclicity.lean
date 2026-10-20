module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity

open CategoryTheory AlgebraicGeometry

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The geometric point obtained by postcomposing its scheme morphism. -/
abbrev GeometricPoint.imageHom {X S : Scheme.{u}} (xbar : GeometricPoint X) (f : X ⟶ S) :
    GeometricPoint S := xbar.map f

end AlgebraicGeometry.Scheme
