module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Normal schemes and irreducible components

This file relates normality to decomposition into pairwise disjoint normal integral open
subschemes when irreducible components are finite on quasi-compact opens.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme admits a pairwise disjoint open cover by normal integral open subschemes when it has
an indexed open covering whose distinct members are disjoint and whose associated open subschemes
are both integral and normal. -/
abbrev HasPairwiseDisjointOpenCoverByNormalIntegral : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens),
    TopologicalSpace.IsOpenCover U ∧
      Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
        ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal

/-- The pairwise disjoint normal integral open-cover property unfolds to its indexed cover data. -/
@[simp]
theorem hasPairwiseDisjointOpenCoverByNormalIntegral_iff :
    X.HasPairwiseDisjointOpenCoverByNormalIntegral ↔
      ∃ (ι : Type u) (U : ι → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
            ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal :=
  Iff.rfl

/-- A scheme admits a finite pairwise disjoint open cover by normal integral open subschemes. -/
abbrev HasFinitePairwiseDisjointOpenCoverByNormalIntegral : Prop :=
  ∃ n : ℕ, ∃ U : Fin n → X.Opens,
    TopologicalSpace.IsOpenCover U ∧
      Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
        ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal

/-- The finite pairwise disjoint normal integral open-cover property unfolds to its cover data. -/
theorem hasFinitePairwiseDisjointOpenCoverByNormalIntegral_iff :
    X.HasFinitePairwiseDisjointOpenCoverByNormalIntegral ↔
      ∃ n : ℕ, ∃ U : Fin n → X.Opens,
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
            ∀ i, AlgebraicGeometry.IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal := sorry

/-- A scheme covered by pairwise disjoint normal integral open subschemes is normal. -/
theorem HasPairwiseDisjointOpenCoverByNormalIntegral.isNormal
    {X : Scheme.{u}} (hX : X.HasPairwiseDisjointOpenCoverByNormalIntegral) :
    X.isNormal := sorry

/-- A scheme whose quasi-compact opens have finitely many irreducible components is normal if and
only if it admits a pairwise disjoint open cover by normal integral open subschemes. -/
theorem isNormal_iff_hasPairwiseDisjointOpenCoverByNormalIntegral
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.isNormal ↔ X.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

end AlgebraicGeometry.Scheme
