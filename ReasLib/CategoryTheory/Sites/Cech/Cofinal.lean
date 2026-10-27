/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology vanishing from cofinal Čech systems

This file packages cofinal covering systems at the site level.  The owners are independent of
ringed spaces and numbered chapters: a system records covering and intersection closure, while
Čech acyclicity adds the coefficient-dependent vanishing condition.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe t w v u

namespace CategoryTheory.Sheaf.Cech

/-- A cofinal system of covers whose iterated Čech intersections remain in a chosen family of
objects. Only selected families need iterated fibre products. Selected covers have index
universe `w`, while cofinality is tested against every covering sieve, independently of `w`. -/
@[stacks 03F9 "cofinal Cech covering systems"]
structure CofinalSystem
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))) : Prop where
  /-- The selected cover carries the finite fibre products used by its Cech nerve. -/
  hasIteratedFiberProducts :
    ∀ ⦃U : C⦄ (cover : FormalCoproduct.{w} (Over U)),
      cover ∈ Cov U → HasIteratedFiberProducts cover.obj
  /-- Every selected family is a cover. -/
  coversTop :
    ∀ ⦃U : C⦄ {cover : FormalCoproduct.{w} (Over U)},
      cover ∈ Cov U → (J.over U).CoversTop cover.obj
  /-- The target of every selected cover belongs to the controlled family. -/
  targets_mem :
    ∀ ⦃U : C⦄ (cover : FormalCoproduct.{w} (Over U)),
      cover ∈ Cov U → U ∈ B
  /-- Every member of a selected cover belongs to the controlled family. -/
  member_mem :
    ∀ ⦃U : C⦄ {cover : FormalCoproduct.{w} (Over U)},
      cover ∈ Cov U → ∀ i : cover.I, (cover.obj i).left ∈ B
  /-- Every iterated intersection of a selected cover belongs to the controlled family.

  The local product witness is installed before the intersection object is formed, so this is
  the same selected product used by the downstream Cech complex. -/
  intersections_mem :
    ∀ ⦃U : C⦄ (cover : FormalCoproduct.{w} (Over U)) (hcover : cover ∈ Cov U),
      letI := hasIteratedFiberProducts cover hcover
      ∀ n : ℕ, ∀ i : (familyPower cover.obj n).I,
        ((familyPower cover.obj n).obj i).left ∈ B
  /-- Every covering sieve of a controlled object contains a selected covering family. -/
  cofinal_sieve :
    ∀ ⦃U : C⦄, U ∈ B → ∀ (S : Sieve U), S ∈ J U →
        ∃ cover : FormalCoproduct.{w} (Over U),
          cover ∈ Cov U ∧ ∀ i : cover.I, S (cover.obj i).hom

namespace CofinalSystem

/-- The target of a selected cover belongs to the controlled family. -/
theorem target_mem
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : CofinalSystem J B Cov) {U : C} (cover : FormalCoproduct.{w} (Over U))
    (hcover : cover ∈ Cov U) : U ∈ B :=
  hCov.targets_mem cover hcover

/-- Each actual member of a selected cover belongs to the controlled family. -/
theorem members_mem
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : CofinalSystem J B Cov) {U : C} {cover : FormalCoproduct.{w} (Over U)}
    (hcover : cover ∈ Cov U) (i : cover.I) : (cover.obj i).left ∈ B :=
  hCov.member_mem hcover i

set_option backward.defeqAttrib.useBackward true in
/-- A selected cover refines a covering family in any index universe. The refinement uses the
existing heterogeneous fixed-target family morphism. -/
theorem exists_family_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : CofinalSystem J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type t} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct.{w} (Over U), cover ∈ Cov U ∧
      Nonempty (SemiRepresentableFamily.Over.Hom
        (⟨cover.I, cover.obj⟩ : SemiRepresentableFamily.Over.Obj U)
        (⟨ι, family⟩ : SemiRepresentableFamily.Over.Obj U)) := by
  classical
  let X : Over U := Over.mk (𝟙 U)
  let S : Sieve U := Sieve.overEquiv X (Sieve.ofObjects family X)
  have hS : S ∈ J U := hfamily X
  obtain ⟨cover, hcover, hmem⟩ := hCov.cofinal_sieve hU S hS
  have hfactor : ∀ a : cover.I, ∃ i : ι, Nonempty (cover.obj a ⟶ family i) := by
    intro a
    have h := (Sieve.overEquiv_iff _ _).mp (hmem a)
    change ∃ i : ι, Nonempty (Over.mk ((cover.obj a).hom ≫ 𝟙 U) ⟶ family i) at h
    obtain ⟨Y, f, hf⟩ := Over.mk_surjective (cover.obj a)
    rw [← hf] at h ⊢
    simpa only [Over.mk_hom, Over.mk_left, Category.comp_id] using h
  choose index hindex using hfactor
  exact ⟨cover, hcover, ⟨{ α := index, f := fun a => Classical.choice (hindex a) }⟩⟩

/-- A cover in a cofinal Čech system refines any given cover in the same index universe. -/
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : CofinalSystem J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type w} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct.{w} (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) := by
  obtain ⟨cover, hcover, ⟨f⟩⟩ := hCov.exists_family_refinement hU family hfamily
  exact ⟨cover, hcover, ⟨{ f := f.α, φ := f.f }⟩⟩

/-- The family form of cofinality, retained for queries in the selected index universe. -/
theorem cofinal
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : CofinalSystem J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type w} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct.{w} (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  hCov.exists_refinement hU family hfamily

end CofinalSystem

/-- An abelian sheaf is Čech-acyclic on a cofinal system when every positive-degree Čech
cohomology object associated to a chosen cover is zero. -/
@[stacks 03F9 "Cech acyclicity on a cofinal covering system"]
structure IsAcyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasProducts.{w} AddCommGrpCat.{v}]
    (F : Sheaf J AddCommGrpCat.{v}) (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))) : Prop
    extends CofinalSystem J B Cov where
  /-- Positive-degree Cech cohomology vanishes on every selected cover, using its local witness. -/
  isZero_cechCohomology :
    ∀ ⦃U : C⦄ {cover : FormalCoproduct.{w} (Over U)},
      (hcover : cover ∈ Cov U) → ∀ {p : ℕ}, 0 < p →
        letI := toCofinalSystem.hasIteratedFiberProducts cover hcover
        IsZero (((FormalCoproduct.cochainComplexFunctor (familyCech cover.obj)).obj
          ((restrictPresheafToOver U).obj
            ((sheafToPresheaf J AddCommGrpCat.{v}).obj F))).homology p)

namespace IsAcyclic

/-- Lemma 21.10.9 (03F9): positive-degree sheaf cohomology vanishes on every object covered by
a cofinal Čech-acyclic system. -/
@[stacks 03F9 "cohomology vanishing from a cofinal Cech-acyclic system"]
theorem isZero_cohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasProducts.{w} AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} {B : Set C}
    {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hF : IsAcyclic F B Cov) {U : C} (hU : U ∈ B) {p : ℕ} (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

end IsAcyclic



end CategoryTheory.Sheaf.Cech
