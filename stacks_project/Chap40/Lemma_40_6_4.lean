module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.TargetLocus
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 40.6.4: If the source and target maps of a groupoid scheme are covers in a standard
topology, the maximal target-open locus on which the source map has a target-local property is
invariant under the groupoid. -/
@[stacks 03JC] #check
  (AlgebraicGeometry.GroupoidScheme.isOpenInvariant_targetLocus_source :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (τ : AlgebraicGeometry.StandardTopology)
      (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
      [P.IsLocalAtTarget τ.precoverage]
      (hs : Presieve.singleton G.s.left ∈ τ.precoverage G.U.left)
      (ht : Presieve.singleton G.t.left ∈ τ.precoverage G.U.left),
      G.toPreRelation.IsOpenInvariant (P.targetLocus G.s.left))
