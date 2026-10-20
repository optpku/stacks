module

public import stacks_project.Chap78.Lemma_78_17_1_Restriction
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.17.3: the notions of restricting groupoids and (pre-)equivalence relations
agree: forgetting a restricted groupoid in algebraic spaces to its underlying
pre-relation agrees with pulling back the underlying pre-relation. -/
@[stacks 044D] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback_toPreRelation :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        (G.pullback g).toPreRelation = G.toPreRelation.pullback g)
