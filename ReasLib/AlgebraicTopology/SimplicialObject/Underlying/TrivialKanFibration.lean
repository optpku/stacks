module

public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.KanFibration
public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration

/-!
# Trivial Kan-fibration properties detected by an underlying simplicial set

This leaf pulls the boundary-inclusion right lifting property back along an arbitrary functor to
types and compares it with the corresponding underlying Kan-fibration property.
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe v u w v' u'

namespace CategoryTheory.SimplicialObject.Underlying

variable {A : Type u} [Category.{v} A]

/-- The morphism property of simplicial maps that become trivial Kan fibrations after applying a
functor `U : A ⥤ Type w` degreewise. -/
@[stacks 08NL "trivial Kan fibrations detected by an underlying simplicial set"]
def trivialKanFibrations (U : A ⥤ Type w) :
    MorphismProperty (SimplicialObject A) :=
  I.rlp.inverseImage ((SimplicialObject.whiskering A (Type w)).obj U)

/-- Membership in `Underlying.trivialKanFibrations U` means that the degreewise image under `U`
has the boundary-inclusion right lifting property. -/
@[simp, stacks 08NL "membership in the underlying trivial Kan-fibration property"]
theorem trivialKanFibrations_iff
    (U : A ⥤ Type w) {X Y : SimplicialObject A} (f : X ⟶ Y) :
    trivialKanFibrations U f ↔ I.rlp (Functor.whiskerRight f U) := sorry

/-- Detecting trivial Kan fibrations through a composite functor is the inverse image of the
property detected after the second functor. -/
@[stacks 08NL "composition of underlying trivial Kan-fibration detectors"]
theorem trivialKanFibrations_comp
    {B : Type u'} [Category.{v'} B] (F : A ⥤ B) (U : B ⥤ Type w) :
    trivialKanFibrations (F ⋙ U) =
      (trivialKanFibrations U).inverseImage
        ((SimplicialObject.whiskering A B).obj F) := sorry

namespace trivialKanFibrations

/-- Every simplicial map detected as a trivial Kan fibration is detected as a Kan fibration by
the same underlying functor. -/
@[stacks 08NL "underlying trivial Kan fibrations are underlying Kan fibrations"]
theorem le_fibrations (U : A ⥤ Type w) :
    trivialKanFibrations U ≤ fibrations U := sorry

end trivialKanFibrations

end CategoryTheory.SimplicialObject.Underlying
