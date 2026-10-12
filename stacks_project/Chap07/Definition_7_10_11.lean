/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (ℱ : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.10.11: the sheaf associated to a set-valued presheaf `ℱ` is the
double-plus presheaf `ℱ⁺⁺`. -/
@[stacks 00WG] #check (CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J
  (CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J ℱ) :
  Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.10.11: the sheaf associated to `ℱ` is equipped with the canonical
map `ℱ ⟶ ℱ⁺⁺` given by the composite of the two plus maps. -/
@[stacks 00WG] #check (CategoryTheory.GrothendieckTopology.TypeSheafification.toPlus J ℱ ≫
  CategoryTheory.GrothendieckTopology.TypeSheafification.toPlus J
    (CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J ℱ) :
  ℱ ⟶ CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J
    (CategoryTheory.GrothendieckTopology.TypeSheafification.plusObj J ℱ))
