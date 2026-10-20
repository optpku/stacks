module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.CategoryTheory.HomRel.Functor
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The simplicial homotopy congruence

The zigzag simplicial homotopy relation is isolated here so that both the homotopy category and
homotopy-equivalence APIs can depend on the relation without depending on one another.
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory.SimplicialObject

/-- The hom-set relation on simplicial objects given by zigzag simplicial homotopy. -/
@[stacks 08RJ "simplicial homotopy congruence relation"]
def homotopyRel (C : Type u) [Category.{v} C] : HomRel (SimplicialObject C) :=
  fun _ _ ↦ Homotopic

/-- Membership in `homotopyRel C` is simplicial homotopy. -/
@[simp, stacks 08RJ "membership in the simplicial homotopy relation"]
theorem homotopyRel_iff {C : Type u} [Category.{v} C]
    {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    homotopyRel C f g ↔ Homotopic f g := sorry

namespace homotopyRel

namespace whiskeringRight

/-- Degreewise application of a functor preserves the simplicial homotopy relation. -/
@[stacks 019Y "functors map the simplicial homotopy relation"]
instance isMappedBy {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    HomRel.IsMappedBy (homotopyRel C)
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ C D).obj F) (homotopyRel D) := sorry

end whiskeringRight

/-- Zigzag simplicial homotopy is a congruence on morphisms of simplicial objects. -/
@[stacks 08RJ "simplicial homotopy is compatible with composition"]
instance congruence (C : Type u) [Category.{v} C] :
    Congruence (homotopyRel C) := sorry

end homotopyRel

end CategoryTheory.SimplicialObject
