/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived categories of presheaf modules

This file installs the standard homology and derived-category structures for presheaves of
modules over a ring-valued presheaf. They are canonical support instances shared by derived
functors whose source is a presheaf-module category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- The canonical homology structure on a category of presheaf modules. -/
instance categoryWithHomology (R : Cᵒᵖ ⥤ RingCat.{w}) :
    CategoryWithHomology (PresheafOfModules.{w} R) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category structure on a category of presheaf modules. -/
@[stacks 05RR "derived category of presheaf modules"]
instance hasDerivedCategory (R : Cᵒᵖ ⥤ RingCat.{w})
    [CategoryWithHomology (PresheafOfModules.{w} R)] :
    HasDerivedCategory (PresheafOfModules.{w} R) :=
  HasDerivedCategory.standard (PresheafOfModules.{w} R)

end PresheafOfModules

namespace ModuleCat.Presheaf

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [Ring B]

/-- The canonical homology structure on `B`-module-valued presheaves. -/
instance categoryWithHomology : CategoryWithHomology (Presheaf C B) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category model for `B`-module-valued presheaves.

The instance is deliberately restricted to this named presentation.  Other derived-category
models remain explicit `[HasDerivedCategory]` inputs to comparison APIs. -/
@[stacks 05RR "derived category of module-valued presheaves"]
instance hasDerivedCategory : HasDerivedCategory (Presheaf C B) :=
  HasDerivedCategory.standard (Presheaf C B)

end ModuleCat.Presheaf
