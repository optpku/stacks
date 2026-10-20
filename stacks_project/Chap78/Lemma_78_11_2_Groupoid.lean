module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap78.Definition_78_4_1_PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation

/-!
# Pre-relations of groupoids in algebraic spaces

This module records the forgetful map sending a groupoid in algebraic spaces over `B`
to the pre-relation `j = (t, s) : R ⟶ U ⨯ U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → AlgebraicSpace.PreRelation G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_hom :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B),
    G.toPreRelation.hom = prod.lift G.t G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_t :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B), G.toPreRelation.t = G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_s :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B), G.toPreRelation.s = G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_isPreEquivalence :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B), G.toPreRelation.IsPreEquivalence)

end AlgebraicGeometry.GroupoidAlgebraicSpace
