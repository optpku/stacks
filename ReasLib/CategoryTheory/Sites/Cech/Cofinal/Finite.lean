/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite cofinal Cech systems

This leaf adds the finite-cover strengthening of `CofinalSystem`.  The system itself is
coefficient-independent; the cohomology comparison is kept as a separate theorem so the same
covering data can be reused with different abelian coefficients and filtered diagrams.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i vi w z v u

namespace CategoryTheory.Sheaf.Cech.CofinalSystem

variable {C : Type u} [Category.{v} C]

/- Finiteness is orthogonal to the inherited target, member and Cech-intersection conditions. -/
/- A nested namespace keeps the public names short while retaining the `CofinalSystem` context. -/

/-- A cofinal Cech system whose selected covers are finite and remain in the chosen family. -/
@[stacks 0739 "finite cofinal Cech covering systems"]
structure FiniteCoverings
    (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))) : Prop
    extends CofinalSystem J B Cov where
  /-- Every selected cover has finite index. -/
  finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct.{w} (Over U)),
    cover ∈ Cov U → Finite cover.I

namespace FiniteCoverings

/-- Each member of a selected cover belongs to the chosen family. -/
theorem members_mem
    {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : FiniteCoverings J B Cov)
    {U : C} {cover : FormalCoproduct.{w} (Over U)} (hcover : cover ∈ Cov U) (i : cover.I) :
    (cover.obj i).left ∈ B := hCov.toCofinalSystem.members_mem hcover i

/-- The target of a selected finite cover belongs to the chosen family. -/
theorem target_mem
    {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : FiniteCoverings J B Cov) {U : C} (cover : FormalCoproduct.{w} (Over U))
    (hcover : cover ∈ Cov U) : U ∈ B := hCov.toCofinalSystem.target_mem cover hcover

/-- A finite cofinal system refines every covering family over a chosen object. -/
theorem exists_refinement
    {J : GrothendieckTopology C}
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U))}
    (hCov : FiniteCoverings J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type w} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct.{w} (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  hCov.toCofinalSystem.exists_refinement hU family hfamily

end FiniteCoverings

section Cohomology

variable {J : GrothendieckTopology C}
variable {I : Type i} [Category.{vi} I] [IsFiltered I]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]

/-- Filtered colimits commute with cohomology on the objects controlled by a finite cofinal system. -/
@[stacks 0739 "cohomology commutes with filtered colimits on finite cofinal systems"]
theorem cohomologyOverColimitComparison_isIso
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct.{w} (Over U)))
    (hCov : FiniteCoverings J B Cov)
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.cohomologyPresheafFunctor.{z, v, u} J p)]
    {U : C} (hU : U ∈ B) :
    IsIso ((colimit.post ℱ (Sheaf.cohomologyPresheafFunctor.{z, v, u} J p)).app (op U)) := sorry

end Cohomology

end CategoryTheory.Sheaf.Cech.CofinalSystem

end
