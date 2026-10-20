module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.Intersection
import StacksCheckRecall

public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.23.4: for proper closed subvarieties `Y` and `Z` of `ℙ(V)`, there is a
nonempty Zariski-open locus of closed centers `p` such that the points of `Y` whose
projection lies in the projection of `Z` are the union of `Y ∩ Z` and a closed locus
of dimension at most `dim(Y) + dim(Z) + 1 - n`. -/
@[stacks 0B1R]
#check
  (@AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.exists_open_coincidenceLocus_eq_union :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (n : ℕ) (hV : Module.finrank k V = n + 1)
      (Y Z : SchemeOverField k) [Variety Y] [Variety Z]
      (iY : Y ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
      (iZ : Z ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
      [IsClosedImmersion iY.left] [IsClosedImmersion iZ.left]
      (hY : Set.range iY.left.base ≠ Set.univ)
      (hZ : Set.range iZ.left.base ≠ Set.univ)
      (projection : ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
        IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
          ProjectiveSpace.VectorSpace.LinearProjection k V p),
      ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
        ∀ (p : ProjectiveSpace.VectorSpace.scheme k V), p ∈ U →
          (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V))) →
            p ∉ Set.range iY.left.base ∧ p ∉ Set.range iZ.left.base ∧
              ∀ (hpY : p ∉ Set.range iY.left.base) (hpZ : p ∉ Set.range iZ.left.base),
                ∃ E : TopologicalSpace.Closeds Y.left,
                  ProjectiveSpace.VectorSpace.LinearProjection.coincidenceLocus
                      ((projection p hp).restrict iY.left
                        ((projection p hp).range_subset_domain iY.left hpY))
                      ((projection p hp).restrict iZ.left
                        ((projection p hp).range_subset_domain iZ.left hpZ)) =
                      iY.left.base ⁻¹' Set.range iZ.left.base ∪ (E : Set Y.left) ∧
                    topologicalKrullDim (E : Set Y.left) + (n : WithBot ℕ∞) ≤
                      topologicalKrullDim Y.left + topologicalKrullDim Z.left + 1)
