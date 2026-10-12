/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Equivalence

/-!
# Restriction from filtered-colimit-preserving functors

Restriction along a small subcategory of finitely presentable filtered generators is an
equivalence on filtered-colimit-preserving functors.  Object and morphism computations for the
restriction functor are part of the public interface.
-/

@[expose] public section

open CategoryTheory.Limits
open Cardinal

universe w vC uC vD uD

-- Local instance justification (search instability): mathlib deliberately keeps the regularity fact for `ℵ₀` out of global instance search and installs `Cardinal.fact_isRegular_aleph0` locally in its presentability modules. This owner is also intrinsically `ℵ₀`-specific, so retaining the same narrow registration avoids both a spurious consumer parameter and global instance pollution.
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace CategoryTheory.ObjectProperty

variable {C : Type uC} [Category.{vC} C]
variable {P : ObjectProperty C}

/-- Restriction from functors preserving `w`-small filtered colimits to functors on the full
subcategory selected by `P`. -/
def filteredColimitRestriction
    (P : ObjectProperty C) (D : Type uD) [Category.{vD} D] :
    ObjectProperty.FullSubcategory
        (fun F : C ⥤ D => PreservesFilteredColimitsOfSize.{w, w} F) ⥤
      (P.FullSubcategory ⥤ D) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringLeft P.FullSubcategory C D).obj P.ι

/-- Restriction acts on an object by precomposition with the full-subcategory inclusion. -/
@[simp]
theorem filteredColimitRestriction_obj
    (P : ObjectProperty C) (D : Type uD) [Category.{vD} D]
    (F : ObjectProperty.FullSubcategory
      (fun G : C ⥤ D => PreservesFilteredColimitsOfSize.{w, w} G)) :
    (filteredColimitRestriction.{w} P D).obj F = P.ι ⋙ F.obj := sorry

/-- Restriction acts on a natural transformation by left whiskering with the inclusion. -/
@[simp]
theorem filteredColimitRestriction_map
    (P : ObjectProperty C) (D : Type uD) [Category.{vD} D]
    {F G : ObjectProperty.FullSubcategory
      (fun K : C ⥤ D => PreservesFilteredColimitsOfSize.{w, w} K)}
    (α : F ⟶ G) :
    (filteredColimitRestriction.{w} P D).map α =
      Functor.whiskerLeft P.ι α.hom := sorry

namespace IsCardinalFilteredGenerator

/-- Restriction is an equivalence when `P` is a small family of finitely presentable filtered
generators and both categories have the relevant filtered colimits. -/
@[stacks 0FWY]
theorem restrictionIsEquivalence
    [LocallySmall.{w} C] [ObjectProperty.Small.{w} P]
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    (D : Type uD) [Category.{vD} D]
    [HasFilteredColimitsOfSize.{w, w} C]
    [HasFilteredColimitsOfSize.{w, w} D] :
    Functor.IsEquivalence (filteredColimitRestriction.{w} P D) := sorry

end IsCardinalFilteredGenerator

end CategoryTheory.ObjectProperty
