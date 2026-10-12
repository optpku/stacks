/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_AtlasSiteCover
public import stacks_project.Chap108.Lemma_108_4_9_DenseSiteComposition
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

/-- Mathlib's affine basis stays cover dense after passing to its proved small model. -/
theorem schemeAffineCoverDense (S : Scheme.{u}) :
    (schemeAffineInclusion S).IsCoverDense S.smallEtaleTopology :=
  coverDense_precomp_equivalence (equivSmallModel S.AffineEtale).symm
    (Scheme.AffineEtale.Spec S) S.smallEtaleTopology

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The actual small affine chart family is cover dense in the original site. -/
theorem spaceAffineCoverDense :
    (spaceAffineInclusion X).IsCoverDense (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := schemeAffineCoverDense (atlasScheme X).left
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := atlasEtaleFunctorCoverDense X
  exact coverDense_comp _ _ (atlasScheme X).left.smallEtaleTopology
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) (atlasEtaleFunctorCoverPreserving X)

/-- All original-site morphisms between this small set of actual affine charts. -/
abbrev SpaceAffineBasis := InducedCategory
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X) (spaceAffineInclusion X).obj

/-- The fully faithful inclusion has explicit original morphisms as its Hom data. -/
noncomputable def spaceBasisInclusion : SpaceAffineBasis X ⥤
    AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X := inducedFunctor (spaceAffineInclusion X).obj

/-- Adding all actual chart morphisms preserves the proven object-covering property. -/
theorem spaceBasisCoverDense :
    (spaceBasisInclusion X).IsCoverDense (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) where
  is_cover V := by
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceAffineCoverDense X
    apply (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X).superset_covering _
      ((spaceAffineInclusion X).is_cover_of_isCoverDense
        (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) V)
    rintro W f ⟨⟨d, a, b, hab⟩⟩
    exact ⟨⟨(show SpaceAffineBasis X from d), a, b, hab⟩⟩

/-- The small basis carries the topology induced from the original site. -/
noncomputable def spaceBasisTopology : GrothendieckTopology (SpaceAffineBasis X) :=
  (spaceBasisInclusion X).inducedTopology (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
