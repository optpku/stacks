module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Unramified and locally quasi-finite pseudo-torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- A pseudo-torsor under a group algebraic space is unramified over the base
if the group is unramified over the base and both are locally of finite type
over the base. -/
instance unramified_of_isPseudoTorsor {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} (X : Action G) [Mod.IsPseudoTorsor X]
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.Unramified G.X.hom] :
    AlgebraicSpace.Unramified X.X.hom := sorry

/-- A pseudo-torsor under a group algebraic space is locally quasi-finite over
the base if the group is locally quasi-finite over the base and both are locally
of finite type over the base. -/
instance locallyQuasiFinite_of_isPseudoTorsor {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B} (X : Action G)
    [Mod.IsPseudoTorsor X] [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.LocallyQuasiFinite G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite X.X.hom := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
