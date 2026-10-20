module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-!
# Colimits of equivariant quasi-coherent modules on groupoids in algebraic spaces

The category of equivariant quasi-coherent modules on a groupoid in algebraic spaces
admits all same-universe small colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/-- Equivariant quasi-coherent modules on a groupoid in algebraic spaces admit all
same-universe small colimits. -/
theorem hasColimitsOfSize {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : HasColimitsOfSize.{u, u} G.QCoh := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
