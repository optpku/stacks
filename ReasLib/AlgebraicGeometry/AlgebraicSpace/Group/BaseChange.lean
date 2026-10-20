module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange

/-! Base change of internal group objects in slices of algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Pulling back an internal group object over `B` along `f : B' ⟶ B` gives an internal
group object over `B'`. -/
def baseChange {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (f : B' ⟶ B) : GroupAlgebraicSpace B' :=
  (Over.pullback f).mapGrp.obj G

/-- Base change of a group algebraic space locally of finite type is locally of finite type. -/
instance locallyOfFiniteType_baseChange {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyOfFiniteType (baseChange G g).X.hom :=
  AlgebraicSpace.LocallyOfFiniteType.pullback_snd
    (inferInstance : AlgebraicSpace.LocallyOfFiniteType G.X.hom) g

end AlgebraicGeometry.GroupAlgebraicSpace
