module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# Unramified and locally quasi-finite group algebraic spaces

The structure morphism of a group algebraic space locally of finite type is
unramified (resp. locally quasi-finite) if and only if it is unramified
(resp. quasi-finite) at the identity-section point of every point of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The structure morphism of a group algebraic space locally of finite type is
unramified if and only if it is unramified at the identity-section point of
every point of the base. -/
theorem unramified_iff_unramifiedAt_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.Unramified G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.UnramifiedAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b) :=
  sorry

/-- The structure morphism of a group algebraic space locally of finite type is
locally quasi-finite if and only if it is quasi-finite at the identity-section
point of every point of the base. -/
theorem locallyQuasiFinite_iff_quasiFiniteAt_one {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.QuasiFiniteAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b) :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
