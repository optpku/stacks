module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Remark_85_5_1_Morphism

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTotalMorphism

/-!
# Total morphisms of fiberwise simplicial sites

The shared site API provides the total morphism and its comparisons. The total-functor
and fiber-inclusion aliases retain the established source-facing interface.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory.Grothendieck.IsFiberwiseMorphism

variable {F F' : SimplicialObject Cat.{v, u}} (α : F ⟶ F')

/-- The functor `v_total : C_total ⥤ C'_total` obtained by applying the component functors
of `α` in each degree. -/
abbrev totalFunctor : Grothendieck F ⥤ Grothendieck F' :=
  Grothendieck.map α

/-- The fiber inclusion of `F` followed by `v_total` is the component functor followed by
the fiber inclusion of `F'`. -/
def totalFunctor_comp_ι (n : SimplexCategory) :
    ι F (op n) ⋙ totalFunctor α ≅ (α.app (op n)).toFunctor ⋙ ι F' (op n) :=
  Grothendieck.ιCompMap α (op n)

end CategoryTheory.Grothendieck.IsFiberwiseMorphism
