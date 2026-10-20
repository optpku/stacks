/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Derived
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of derived and bar fiber homology

This leaf records the comparison at the object, presheaf, sheaf, and coefficient-functor levels.
The functor-category statements are the reusable bridges; objectwise theorems remain available
for direct fiber calculations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX w

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Computation

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable [UnivLE.{max wX vX, w}]
variable [∀ V : C,
  HasProjectiveResolutions ((X.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{w})]
variable [∀ V : C,
  HasColimitsOfShape (X.p.Fiber V)ᵒᵖ AddCommGrpCat.{w}]

/-- Derived-colimit homology on one fiber is represented by the bar complex. -/
@[stacks 08PG "derived and bar fiber category homology comparison"]
theorem homology_isomorphic_bar
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : C) (n : ℕ) :
    IsIsomorphic (Derived.homology X F V n) (Bar.homology X F V n) := sorry

section Presheaf

variable [Presheaf.PreservesProjectiveReindex X AddCommGrpCat.{w}]

/-- The derived-colimit and bar constructions give isomorphic fiber-homology presheaves. -/
@[stacks 08PG "derived and bar fiber homology presheaf comparison"]
theorem presheaf_isomorphic_bar
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic (Derived.presheaf X F n) (Bar.presheaf X F n) := sorry

/-- The derived and bar constructions are isomorphic as functors in the coefficient presheaf. -/
@[stacks 08PG "derived and bar fiber homology presheaf functor comparison"]
theorem presheafFunctor_isomorphic_bar (n : ℕ) :
    IsIsomorphic (Derived.presheafFunctor X n) (Bar.presheafFunctor X n) := sorry

section Sheaf

variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafifying the derived-colimit and bar fiber-homology presheaves gives isomorphic sheaves. -/
@[stacks 08PG "derived and bar fiber homology sheaf comparison"]
theorem sheaf_isomorphic_bar
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic (Derived.sheaf J X F n) (Bar.sheaf J X F n) := sorry

/-- The derived and bar constructions are isomorphic as sheaf-valued coefficient functors. -/
@[stacks 08PG "derived and bar fiber homology sheaf functor comparison"]
theorem sheafFunctor_isomorphic_bar (n : ℕ) :
    IsIsomorphic (Derived.sheafFunctor J X n) (Bar.sheafFunctor J X n) := sorry

end Sheaf
end Presheaf
end CategoryTheory.FiberedCategoryOver.FiberHomology.Computation
