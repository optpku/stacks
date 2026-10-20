module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Comparison
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Maps of quotients of groupoids in functors

A morphism of groupoids in functors induces a functor between their
Grothendieck constructions commuting strictly with projection to the base.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- A morphism of groupoids in functors induces a morphism of their quotients over the base. -/
def Hom.toQuotientBasedFunctor
    {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    BasedCategory.ofFunctor (Grothendieck.forget (G.toFunctor ⋙ Grpd.forgetToCat)) ⟶
      BasedCategory.ofFunctor (Grothendieck.forget (H.toFunctor ⋙ Grpd.forgetToCat)) :=
  BasedFunctor.ofFunctor
    (Grothendieck.map (Functor.whiskerRight f.toNatTrans Grpd.forgetToCat))
    Grothendieck.functor_comp_forget

/-- The underlying functor of the induced quotient map is the Grothendieck map
of the associated natural transformation of fibre-groupoid functors. -/
theorem Hom.toQuotientBasedFunctor_toFunctor
    {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    (toQuotientBasedFunctor f).toFunctor =
      Grothendieck.map (Functor.whiskerRight f.toNatTrans Grpd.forgetToCat) := rfl

end CategoryTheory.GroupoidInFunctors
