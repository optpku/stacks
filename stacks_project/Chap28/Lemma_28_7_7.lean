module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.LocallyNoetherian
import stacks_project.Chap28.Lemma_28_7_6
import StacksCheckRecall

universe u

/- Lemma 28.7.7: a locally Noetherian scheme is normal if and only if it is a disjoint union of
integral normal schemes, expressed as a pairwise disjoint open cover by open subschemes that are
both integral and normal. -/
@[stacks 033N] #check
  (AlgebraicGeometry.IsLocallyNoetherian.isNormal_iff_hasPairwiseDisjointOpenCoverByNormalIntegral :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal ↔
        ∃ (ι : Type u) (U : ι → X.Opens),
          TopologicalSpace.IsOpenCover U ∧
            Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
              ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧
                (U i).toScheme.isNormal)
