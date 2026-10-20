/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.FixedTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite fixed-target cofinal Cech systems

This leaf is the universe-polymorphic, fixed-target form of Lemma 21.16.1.  Finiteness is a
property of each selected cover; no finite-product instance is required for unrelated slices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i vi z w v u

namespace CategoryTheory.Sheaf.Cech.FixedTarget

variable {C : Type u} [Category.{v} C]

/-- A fixed-target cofinal Cech system whose selected covers have finite index. -/
@[stacks 0739 "finite fixed-target cofinal Cech system"]
structure FiniteCoverings
    (J : GrothendieckTopology C) (B : Set C)
    (Cov : ∀ U : C, Set (Cover.{w} U)) : Prop
    extends CofinalSystem J B Cov where
  /-- Every selected cover has finite index. -/
  finite : ∀ ⦃U : C⦄ {cover : Cover.{w} U}, cover ∈ Cov U →
    Finite cover.toFormalCoproduct.I

namespace FiniteCoverings

/-- Every member of a selected finite cover lies in the controlled object family. -/
theorem members_mem
    {J : GrothendieckTopology C} {B : Set C}
    {Cov : ∀ U : C, Set (Cover.{w} U)}
    (hCov : FiniteCoverings J B Cov) {U : C} {cover : Cover.{w} U}
    (hcover : cover ∈ Cov U) (i : cover.toFormalCoproduct.I) :
    (cover.family i).left ∈ B := sorry

/-- A finite fixed-target cofinal system refines every covering family over a controlled object. -/
theorem exists_refinement
    {J : GrothendieckTopology C} {B : Set C}
    {Cov : ∀ U : C, Set (Cover.{w} U)}
    (hCov : FiniteCoverings J B Cov) {U : C} (hU : U ∈ B)
    (family : FormalCoproduct.{w} (Over U)) (hfamily : (J.over U).CoversTop family.obj) :
    ∃ cover : Cover.{w} U,
      cover ∈ Cov U ∧ Nonempty (cover.toFormalCoproduct ⟶ family) := sorry

end FiniteCoverings

section Cohomology

variable {J : GrothendieckTopology C}
variable {I : Type i} [Category.{vi} I] [IsFiltered I]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]

/-- Lemma 21.16.1 (0739): on a finite fixed-target cofinal system, filtered colimits commute with
objectwise sheaf cohomology. -/
@[stacks 0739 "filtered-colimit comparison on a finite fixed-target Cech system"]
theorem cohomologyOverObject_colimitComparison_isIso
    (B : Set C) (Cov : ∀ U : C, Set (Cover.{w} U))
    (hCov : FiniteCoverings J B Cov)
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{max w v}) [HasColimit ℱ] (p : ℕ)
    {U : C}
    [HasColimit (ℱ ⋙ Sheaf.cohomologyOverObjectFunctor.{z, w, v, u} J U p)]
    (hU : U ∈ B) :
    IsIso (colimit.post ℱ (Sheaf.cohomologyOverObjectFunctor.{z, w, v, u} J U p)) := sorry

end Cohomology

end CategoryTheory.Sheaf.Cech.FixedTarget
