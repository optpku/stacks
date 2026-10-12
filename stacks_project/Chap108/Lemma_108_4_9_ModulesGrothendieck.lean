/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_AffineBasis
public import stacks_project.Chap108.Lemma_108_4_9_DenseSheafification
public import stacks_project.Chap108.Lemma_108_4_9_DenseModuleSheaves

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Proved small-universe sheafification on the original algebraic-space etale site. -/
theorem spaceHasSheafify :
    HasSheafify (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u} := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Full := (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).full
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Faithful :=
    (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).faithful
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceBasisCoverDense X
  exact smallDenseSheafification (spaceBasisInclusion X)
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)

/-- The local-bijection characterization uses the same certified small basis. -/
theorem spaceWEquals :
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Full := (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).full
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Faithful :=
    (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).faithful
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceBasisCoverDense X
  exact smallDenseWEquals (spaceBasisInclusion X)
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)

/-- Restriction to the actual small affine basis proves the original sheaf Hom-size bound. -/
theorem spaceSheavesLocallySmall :
    LocallySmall.{u} (Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u}) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Full := (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).full
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Faithful :=
    (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).faithful
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceBasisCoverDense X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).IsDenseSubsite (spaceBasisTopology X)
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) := by
    dsimp only [spaceBasisTopology]
    infer_instance
  exact locallySmall_of_faithful ((spaceBasisInclusion X).sheafPushforwardContinuous
    AddCommGrpCat.{u} (spaceBasisTopology X) (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X))

/-- The original unlifted varying-ring module category has a proved generator/AB5 certificate.
The let-bound instances are the certified sheafification above, not the legacy admitted owners. -/
theorem spaceModulesGrothendieck
    (R : Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) RingCat.{u}) :
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceHasSheafify X
    -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
    letI := spaceWEquals X
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceHasSheafify X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceWEquals X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceSheavesLocallySmall X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Full := (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).full
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).Faithful :=
    (fullyFaithfulInducedFunctor (spaceAffineInclusion X).obj).faithful
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := spaceBasisCoverDense X
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (spaceBasisInclusion X).IsDenseSubsite (spaceBasisTopology X)
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) := by
    dsimp only [spaceBasisTopology]
    infer_instance
  exact denseModulesGrothendieck (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) R
    (spaceBasisTopology X) (spaceBasisInclusion X)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
