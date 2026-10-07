module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck

/-!
# Derived categories of abelian sheaves on sites

This file installs the canonical homology and derived-category structures for
abelian sheaves on an arbitrary site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v z

namespace CategoryTheory.AbelianSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{z}]

/-- Abelian sheaves on a site carry the homology structure induced by their abelian category. -/
@[stacks 01DP "abelian-sheaf homology owner"]
instance categoryWithHomology :
    CategoryWithHomology (Sheaf J AddCommGrpCat.{z}) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category structure on abelian sheaves over a site. -/
@[stacks 01DP "abelian-sheaf derived-category owner"]
instance hasDerivedCategory :
    HasDerivedCategory (Sheaf J AddCommGrpCat.{z}) :=
  HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{z})

end CategoryTheory.AbelianSheaf
