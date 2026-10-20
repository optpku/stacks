module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsNoetherian X]

/- Lemma 28.7.6: a Noetherian scheme `X` is normal if and only if `X` is a finite disjoint union
of normal integral schemes, expressed as a finite pairwise disjoint open cover by open subschemes
that are both integral and normal. -/
@[stacks 033M] #check
  (AlgebraicGeometry.Scheme.isNormal_iff_hasFinitePairwiseDisjointOpenCoverByNormalIntegral X :
    X.isNormal ↔
      ∃ n : ℕ, ∃ U : Fin n → X.Opens,
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
            ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧
              (U i).toScheme.isNormal)

end
