module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Directed
import StacksCheckRecall

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open TopologicalSpace

universe u v

/- Lemma 63.3.15: for a separated locally finite-type morphism and an
inclusion-directed open cover, the canonical comparison from the colimit of
restricted compact-support pushforwards to the full pushforward is an
isomorphism, naturally in the abelian étale sheaf. The transitions are the
covariance maps along open immersions. -/
@[stacks 0F54] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekDirectedComparison_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      {ι : Type v} (U : ι → X.Opens)
      [Fact (IsOpenCover U)] [Fact (Directed (· ≤ ·) U)]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      [HasColimit (etaleLowerShriekDirectedDiagram f U F)],
      IsIso (etaleLowerShriekDirectedComparisonApp f U F))
