module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.7.5: if every quasi-compact open of a scheme has finitely many irreducible components,
then the scheme is normal if and only if it admits a pairwise disjoint open cover by normal
integral open subschemes. -/
@[stacks 0357] #check
  (AlgebraicGeometry.Scheme.isNormal_iff_hasPairwiseDisjointOpenCoverByNormalIntegral :
    ∀ (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.isNormal ↔
        ∃ (ι : Type u) (U : ι → X.Opens),
          TopologicalSpace.IsOpenCover U ∧
            Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
              ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal)
