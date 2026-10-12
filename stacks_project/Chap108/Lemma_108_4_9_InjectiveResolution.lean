/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_ModulesGrothendieck
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
  (R : Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) RingCat.{u})

-- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
local instance certifiedSpaceSheafify :
    HasSheafify (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u} :=
  spaceHasSheafify X

-- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
local instance certifiedSpaceWEquals :
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  spaceWEquals X

/-- Actual injective data in the original module universe, using the proved dense-basis certificate. -/
noncomputable def spaceResolution (M : SheafOfModules.{u} R) : InjectiveResolution M := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceHasSheafify X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceWEquals X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceModulesGrothendieck X R
  exact InjectiveResolution.of M

/-- The genuine resolution extended to integer degrees without any universe lift. -/
noncomputable def spaceResolutionComplex (M : SheafOfModules.{u} R) :
    CochainComplex (SheafOfModules.{u} R) ℤ :=
  (spaceResolution X R M).cocomplex.extend ComplexShape.embeddingUpNat

/-- The canonical augmentation from the original single complex M[0]. -/
noncomputable def spaceResolutionMap (M : SheafOfModules.{u} R) :
    (HomologicalComplex.single (SheafOfModules.{u} R) (ComplexShape.up ℤ) 0).obj M ⟶
      spaceResolutionComplex X R M :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (spaceResolution X R M).ι ComplexShape.embeddingUpNat

/-- K-injectivity is proved for the actual target complex. -/
theorem spaceResolutionKInjective (M : SheafOfModules.{u} R) :
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceHasSheafify X
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceWEquals X
    (spaceResolutionComplex X R M).IsKInjective := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceHasSheafify X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceWEquals X
  unfold spaceResolutionComplex
  infer_instance

/-- The actual augmentation is a proved quasi-isomorphism. -/
theorem spaceResolutionQuasiIso (M : SheafOfModules.{u} R) :
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceHasSheafify X
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceWEquals X
    QuasiIso (spaceResolutionMap X R M) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceHasSheafify X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceWEquals X
  have hExtension := (HomologicalComplex.quasiIso_extendMap_iff
    (spaceResolution X R M).ι ComplexShape.embeddingUpNat).2 (spaceResolution X R M).quasiIso
  have hIso := quasiIso_of_isIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv
  unfold spaceResolutionMap
  exact quasiIso_comp _ _ (hφ := hIso) (hφ' := hExtension)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
