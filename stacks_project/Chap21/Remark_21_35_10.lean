module

public import ReasLib.CategoryTheory.Monoidal.Closed.AdjunctionComparison
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.35.10

A left adjoint with an objectwise tensor comparison induces a canonical internal-Hom comparison
for its right adjoint.  This is a generic braided closed-monoidal construction; a derived
pullback/pushforward pair only supplies the adjunction and tensor isomorphism.
-/

/- Remark 21.35.10 (0B6D): the source-order evaluation morphism. -/
@[stacks 0B6D "internal-Hom evaluation"] #check
  @CategoryTheory.Adjunction.derivedInternalHomEvaluation

@[stacks 0B6D "pullback tensor comparison"] #check
  @CategoryTheory.Adjunction.derivedPullbackTensorComparison

@[stacks 0B6D "internal-Hom comparison adjoint map"] #check
  @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparisonAdjointMap

@[stacks 0B6D "derived pushforward internal-Hom comparison"] #check
  @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison

@[stacks 0B6D "derived pushforward internal-Hom comparison specification"] #check
  @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison_spec

/- The evaluation-compatible square is the compositional downstream interface. -/
@[stacks 0B6D "derived pushforward internal-Hom evaluation square"] #check
  @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison_evaluation_commSq
