/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Category of Torsion Abelian Sheaves

This file specializes the generic weak-Serre comparison functor to locally torsion abelian
sheaves.  The chosen ambient and full-subcategory derived categories remain explicit typeclass
inputs.
-/

@[expose] public section

open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.Torsion.DerivedComparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasDerivedCategory.{w} (SiteAbelianSheafCat J)]
variable [HasDerivedCategory.{w} (Sheaf.torsion J).FullSubcategory]

/-- Lemma 21.19.8 (0DD7): the derived category of torsion abelian sheaves is equivalent to the
full subcategory of the ambient derived category whose cohomology sheaves are torsion. -/
@[stacks 0DD7 "derived comparison for torsion abelian sheaves", instance]
theorem isEquivalence :
    Functor.IsEquivalence
      (DerivedCategory.CohomologyIn.Comparison.functor (Sheaf.torsion J)) := sorry

end CategoryTheory.Sheaf.Torsion.DerivedComparison
