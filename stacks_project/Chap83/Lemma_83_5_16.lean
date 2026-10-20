module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoretic
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 83.5.16 (1): a pre-equivalence relation is a set-theoretic
pre-equivalence relation. -/
@[stacks 0492] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_of_isPreEquivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
      P.IsPreEquivalence → P.IsSetTheoreticPreEquivalence)

/- Lemma 83.5.16 (2): an equivalence relation is a set-theoretic equivalence relation. -/
@[stacks 0492] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticEquivalence_of_isEquivalenceRelation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
      [IsEquivalenceRelation P.t P.s], P.IsSetTheoreticEquivalence)

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupoidAlgebraicSpace B)
variable (H : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action H)

-- The pre-relation underlying a groupoid is a set-theoretic pre-equivalence relation.
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_of_isPreEquivalence
    G.toPreRelation (GroupoidAlgebraicSpace.toPreRelation_isPreEquivalence G) :
    G.toPreRelation.IsSetTheoreticPreEquivalence)

-- The same conclusion holds for the canonical groupoid of a group action.
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_of_isPreEquivalence
    (GroupoidAlgebraicSpace.ofAction H X).toPreRelation
    (GroupoidAlgebraicSpace.toPreRelation_isPreEquivalence
      (GroupoidAlgebraicSpace.ofAction H X)) :
    (GroupoidAlgebraicSpace.ofAction H X).toPreRelation.IsSetTheoreticPreEquivalence)
