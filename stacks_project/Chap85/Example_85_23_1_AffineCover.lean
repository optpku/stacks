/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Affine coverings in the spaces-étale site

Affine covering families in `spacesEtaleSite X` are the chosen system `Cov_V` of
étale coverings with affine members. Every object admits such a covering, the
system is cofinal among spaces-étale coverings, and quasi-coherent cohomology
vanishes in positive degrees on affine algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Morphisms in the spaces-étale site are étale as morphisms of algebraic spaces. -/
instance etale_spacesEtaleSite_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (f : U ⟶ V) : Etale f.left :=
  sorry

/-- A displayed family in `spacesEtaleSite X` is an affine covering when it covers in
`spacesEtalePrecoverage` and every member is an affine algebraic space. -/
def IsAffineCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
    {ι : Type u} (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V) : Prop :=
  Presieve.ofArrows U f ∈ spacesEtalePrecoverage X V ∧ ∀ i, IsAffine (U i).left

/-- Affine covering families are exactly the spaces-étale covering families whose members
are affine algebraic spaces. -/
theorem isAffineCovering_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
    {ι : Type u} (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V) :
    IsAffineCovering U f ↔
      Presieve.ofArrows U f ∈ spacesEtalePrecoverage X V ∧ ∀ i, IsAffine (U i).left :=
  sorry

/-- Every object of the spaces-étale site admits an affine covering family. -/
theorem exists_affineCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : spacesEtaleSite X) :
    ∃ (ι : Type u) (_ : Small.{u} ι) (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V),
      IsAffineCovering U f :=
  sorry

/-- Affine covering families are cofinal among spaces-étale coverings. -/
theorem exists_affineCovering_refinement {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : spacesEtaleSite X} {ι : Type u} [Small.{u} ι] {W : ι → spacesEtaleSite X}
    (g : ∀ i, W i ⟶ V) (hg : Presieve.ofArrows W g ∈ spacesEtalePrecoverage X V) :
    ∃ (κ : Type u) (_ : Small.{u} κ) (U : κ → spacesEtaleSite X) (f : ∀ k, U k ⟶ V),
      IsAffineCovering U f ∧ (Presieve.ofArrows U f).FactorsThru (Presieve.ofArrows W g) :=
  sorry

/-- Higher cohomology of a quasi-coherent module on an affine algebraic space vanishes. -/
theorem higherCohomology_isZero_of_isAffine {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})]
    [IsAffine Y] (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (cohomology Y F p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
