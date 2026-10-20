module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.LeftDerived

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]

/-- Category homology of a `B`-module-valued presheaf, as the left-derived colimit.
This is the module-coefficient parallel of `categoryHomology`, with values in
`ModuleCat` and the colimit functor derived degree by degree. -/
abbrev moduleHomology {B : Type w} [Ring B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (n : ℕ) : ModuleCat.{w} B :=
  ((colim : (Cᵒᵖ ⥤ ModuleCat.{w} B) ⥤ ModuleCat.{w} B).leftDerived n).obj F

end CategoryTheory.CategoryHomology
