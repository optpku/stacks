/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturally graded tensor products on a ringed site

Finite coproducts and their preservation by tensor products give the canonical monoidal and
symmetric structures on naturally graded module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.NatGraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The canonical monoidal structure on naturally graded module sheaves. -/
@[stacks 0FQW "canonical tensor product on naturally graded module sheaves"]
noncomputable abbrev monoidalCategory :
    MonoidalCategory
      (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) :=
  CategoryTheory.GradedObject.monoidalCategory
    (I := ℕ) (C := ringedSiteModuleCategory.{u, v, w, w} J O)

/-- Typeclass-search bridge to the canonical monoidal structure on naturally graded module
sheaves. -/
@[stacks 0FQW "monoidal instance for naturally graded module sheaves"]
noncomputable instance instMonoidalCategory :
    MonoidalCategory
      (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) :=
  monoidalCategory O

/-- The canonical symmetric structure on naturally graded module sheaves. -/
@[stacks 0FQW "canonical symmetry on naturally graded module sheaves"]
noncomputable abbrev symmetricCategory :
    SymmetricCategory
      (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) :=
  CategoryTheory.GradedObject.symmetricCategory
    (I := ℕ) (C := ringedSiteModuleCategory.{u, v, w, w} J O)

/-- Typeclass-search bridge to the canonical symmetric structure on naturally graded module
sheaves. -/
@[stacks 0FQW "symmetric instance for naturally graded module sheaves"]
noncomputable instance instSymmetricCategory :
    SymmetricCategory
      (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) :=
  symmetricCategory O

end SheafOfModules.RingedSite.NatGraded
