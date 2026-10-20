/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian.Comparison
import StacksCheckRecall

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

/- Lemma 59.18.6 (Tag 03OQ): the fixed-target free-abelian Cech complex is exact in every
   positive degree, equivalently its positive-degree homology objects vanish. -/
@[stacks 03OQ]
#check (CategoryTheory.Cech.FreeAbelian.coverComplex_homology_isZero_succ :
  ∀ {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family]
    [HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})] (i : ℕ),
    IsZero ((CategoryTheory.Cech.FreeAbelian.coverComplex family).homology (i + 1)))

#check @CategoryTheory.Cech.FreeAbelian.coverComplex_homology_isZero_of_pos

end
