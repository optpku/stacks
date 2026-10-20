module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.17.5: a nonempty scheme-theoretic relation fibre is an fpqc torsor under
its fibre stabilizer over the residue field. -/
@[stacks 04Q3] #check
  (AlgebraicGeometry.GroupoidScheme.RelationAction.fiberAction_isTorsor :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (Q : AlgebraicGeometry.GroupoidScheme S)
      (p : (Q.U ⨯ Q.U).left),
      Nonempty ((Over.Hom.left Q.toPreRelation.hom).fiber p) →
        AlgebraicGeometry.GroupScheme.IsTorsor
          (AlgebraicGeometry.GroupoidScheme.RelationAction.fiberGroup Q p)
          (AlgebraicGeometry.GroupoidScheme.RelationAction.fiberAction Q p))
