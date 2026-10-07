module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kan-fibration properties detected by an underlying simplicial set

Any functor to types sends simplicial objects and their morphisms to simplicial sets. This leaf
owns the inverse-image morphism property for maps that become Kan fibrations, independently of
the algebraic structure later used to prove membership in it.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe v u w v' u'

namespace CategoryTheory.SimplicialObject.Underlying

variable {A : Type u} [Category.{v} A]

/-- The morphism property of simplicial maps that become Kan fibrations after applying a functor
`U : A ⥤ Type w` degreewise. -/
@[stacks 08P0 "Kan fibrations detected by an underlying simplicial set"]
def fibrations (U : A ⥤ Type w) : MorphismProperty (SimplicialObject A) :=
  (HomotopicalAlgebra.fibrations SSet.{w}).inverseImage
    ((SimplicialObject.whiskering A (Type w)).obj U)

/-- Membership in `Underlying.fibrations U` means that the degreewise image under `U` is a Kan
fibration of simplicial sets. -/
@[simp, stacks 08P0 "membership in the underlying Kan-fibration property"]
theorem fibrations_iff (U : A ⥤ Type w) {X Y : SimplicialObject A} (f : X ⟶ Y) :
    fibrations U f ↔ Fibration (Functor.whiskerRight f U) := sorry

/-- Detecting Kan fibrations through a composite functor is the inverse image of the property
detected after the second functor. -/
@[stacks 08P0 "composition of underlying Kan-fibration detectors"]
theorem fibrations_comp
    {B : Type u'} [Category.{v'} B] (F : A ⥤ B) (U : B ⥤ Type w) :
    fibrations (F ⋙ U) =
      (fibrations U).inverseImage ((SimplicialObject.whiskering A B).obj F) := sorry

end CategoryTheory.SimplicialObject.Underlying
