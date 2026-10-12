/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A kernel presentation along a family of additive-group-valued functors preserves
filtered colimits when every member of the presenting family does. -/
theorem Adequate.preservesFilteredColimits
    {A : CommRingCat.{u}}
    {underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})}
    {F : Under A ⥤ AddCommGrpCat.{u}}
    (hF : Adequate A underline F)
    [∀ M, PreservesFilteredColimits (underline.obj M)] :
    PreservesFilteredColimits F := sorry
