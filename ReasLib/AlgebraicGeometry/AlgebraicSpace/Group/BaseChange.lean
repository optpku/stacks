module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group

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

end AlgebraicGeometry.GroupAlgebraicSpace
