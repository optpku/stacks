/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive and Module-Valued Eventual Ranges

This leaf refines mathlib's set-valued `Functor.eventualRange` with the
additive-subgroup and submodule structures needed for inverse systems in
algebra and sheaf cohomology.  The underlying stabilization predicate remains
mathlib's `Functor.IsMittagLeffler`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Functor

variable {D : Type*} [Category D]

/-- The eventual range of an additive inverse system, equipped with its
canonical additive-subgroup structure. -/
@[stacks 0595 "additive eventual range"]
def eventualRangeAddSubgroup (F : D ⥤ AddCommGrpCat) (j : D) : AddSubgroup (F.obj j) :=
  ⨅ (i : D) (f : i ⟶ j), (F.map f).hom.range

/-- The carrier of `eventualRangeAddSubgroup` is exactly mathlib's eventual
range of the underlying type-valued functor. -/
@[simp] theorem coe_eventualRangeAddSubgroup (F : D ⥤ AddCommGrpCat) (j : D) :
    ((F.eventualRangeAddSubgroup j : AddSubgroup (F.obj j)) : Set (F.obj j)) =
      (F ⋙ forget AddCommGrpCat).eventualRange j := sorry

/-- Compute the additive eventual range as the intersection of the ranges of
all transition maps into the chosen stage. -/
theorem eventualRangeAddSubgroup_eq_iInf (F : D ⥤ AddCommGrpCat) (j : D) :
    F.eventualRangeAddSubgroup j =
      ⨅ (i : D) (f : i ⟶ j), (F.map f).hom.range := sorry

variable {J : Type u} [Category J]
variable {R : Type v} [Ring R]

/-- The stable image at `i` of a module-valued inverse system is the
intersection of the ranges of all maps into `i`. -/
@[stacks 0595 "module-valued stable image"]
def stableImage (A : J ⥤ ModuleCat R) (i : J) : Submodule R (A.obj i) :=
  ⨅ (j : J) (_f : j ⟶ i), LinearMap.range (A.map _f).hom

/-- Compute the stable image as the intersection of all transition-map
ranges into the chosen stage. -/
theorem stableImage_eq_iInf (A : J ⥤ ModuleCat R) (i : J) :
    A.stableImage i =
      ⨅ (j : J) (f : j ⟶ i), LinearMap.range (A.map f).hom := sorry

/-- Membership in a module-valued stable image is membership in the eventual
range of the underlying type-valued inverse system. -/
theorem mem_stableImage_iff (A : J ⥤ ModuleCat R) {i : J} {x : A.obj i} :
    x ∈ A.stableImage i ↔ x ∈ (A ⋙ forget (ModuleCat R)).eventualRange i := sorry

end CategoryTheory.Functor
