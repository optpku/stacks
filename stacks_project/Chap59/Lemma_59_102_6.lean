module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.102.6: the derived adjunction unit is an isomorphism for bounded-below
complexes of étale abelian sheaves with torsion cohomology. -/
@[stacks 0DE5] #check
  (AlgebraicGeometry.Scheme.PhComparison.plusAAdjunction_unit_isIso :
    ∀ {X : Scheme.{u}}
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K →
        IsIso ((AlgebraicGeometry.Scheme.PhComparison.plusAAdjunction
          (Over.mk (𝟙 X))).unit.app K))

end
