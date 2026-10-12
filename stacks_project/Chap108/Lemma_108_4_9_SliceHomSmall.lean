/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_DenseModuleSheaves
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {D : Type u} [Category.{u} D] {C : Type v} [Category.{u} C]
  (F : D ⥤ C) (J : GrothendieckTopology C) [F.Full] [F.Faithful] [F.IsCoverDense J]

omit [F.Full] [F.Faithful] in
/-- The actual small chart category over an object remains cover dense in the slice site. -/
theorem sliceBasisCoverDense (U : C) :
    (CostructuredArrow.toOver F U).IsCoverDense (J.over U) where
  is_cover V := by
    rw [GrothendieckTopology.mem_over_iff]
    apply J.superset_covering _ (F.is_cover_of_isCoverDense J V.left)
    rintro W k ⟨⟨d, a, b, hab⟩⟩
    rw [Sieve.overEquiv_iff]
    refine ⟨⟨CostructuredArrow.mk (b ≫ V.hom),
      Over.homMk a ?_, Over.homMk b rfl, ?_⟩⟩
    · exact (Category.assoc _ _ _).symm.trans (congrArg (fun h ↦ h ≫ V.hom) hab)
    · apply Over.OverMorphism.ext
      exact hab

include F in
/-- Hom sets of original coefficient-universe module sheaves on each slice are u-small. -/
theorem sliceModulesLocallySmall (R : Sheaf J RingCat.{u}) (U : C) :
    LocallySmall.{u} (SheafOfModules.{u} (R.over U)) := by
  let G := CostructuredArrow.toOver F U
  let K := G.inducedTopology (J.over U)
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := sliceBasisCoverDense F J U
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : G.IsDenseSubsite K (J.over U) := inferInstance
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : LocallySmall.{u} (Sheaf (J.over U) AddCommGrpCat.{u}) :=
    locallySmall_of_faithful (G.sheafPushforwardContinuous AddCommGrpCat.{u} K (J.over U))
  exact locallySmall_of_faithful (SheafOfModules.toSheaf (R.over U))

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
