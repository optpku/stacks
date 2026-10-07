module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.Algebra.Category.Grp.Presheaf.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived categories of additive presheaves

Additive presheaves form an abelian functor category.  This leaf installs its canonical homology
structure and standard derived-category model once, instead of rebuilding them with local
instances in every cohomological construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AddCommGrpCat.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The canonical homology structure on additive presheaves. -/
instance categoryWithHomology :
    CategoryWithHomology (AddCommGrpCat.Presheaf.{u, v, w} C) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category model for additive presheaves. -/
@[stacks 05RR "derived category of additive presheaves"]
instance hasDerivedCategory :
    HasDerivedCategory (AddCommGrpCat.Presheaf.{u, v, w} C) :=
  HasDerivedCategory.standard (AddCommGrpCat.Presheaf.{u, v, w} C)

end AddCommGrpCat.Presheaf
