/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# Stabilizers of restricted groupoid schemes

This module identifies the stabilizer of a restricted groupoid scheme with the pullback of
the original stabilizer.
-/

@[expose] public section

open CategoryTheory
open CartesianMonoidalCategory MonoidalCategory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The underlying object of the stabilizer of a restriction is canonically isomorphic to
the pullback of the original stabilizer object. -/
def stabilizerPullbackObjectIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.pullback g).stabilizer.X ≅
      ((Over.pullback g).mapGrp.obj G.stabilizer).X :=
  eqToIso (congrArg Scheme.PreRelation.stabilizer (G.pullback_toPreRelation g)) ≪≫
    G.toPreRelation.stabilizerPullbackIso g

/-- The stabilizer pullback object isomorphism preserves the unit. -/
theorem stabilizerPullbackObjectIso_one {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.pullback g).stabilizer.grp.one ≫ (stabilizerPullbackObjectIso G g).hom =
      ((Over.pullback g).mapGrp.obj G.stabilizer).grp.one := sorry

/-- The stabilizer pullback object isomorphism preserves multiplication. -/
theorem stabilizerPullbackObjectIso_mul {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.pullback g).stabilizer.grp.mul ≫ (stabilizerPullbackObjectIso G g).hom =
      ((stabilizerPullbackObjectIso G g).hom ⊗ₘ
        (stabilizerPullbackObjectIso G g).hom) ≫
          ((Over.pullback g).mapGrp.obj G.stabilizer).grp.mul := sorry

/-- Restriction commutes canonically with taking the bundled stabilizer group. -/
def stabilizerPullbackIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (G.pullback g).stabilizer ≅ (Over.pullback g).mapGrp.obj G.stabilizer :=
  Grp.mkIso (stabilizerPullbackObjectIso G g)
    (stabilizerPullbackObjectIso_one G g)
    (stabilizerPullbackObjectIso_mul G g)

end AlgebraicGeometry.GroupoidScheme
