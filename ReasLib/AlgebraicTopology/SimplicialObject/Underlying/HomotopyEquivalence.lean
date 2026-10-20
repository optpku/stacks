module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy equivalences detected by an underlying simplicial set

Any functor to types sends simplicial objects and their morphisms to simplicial sets. This leaf
owns the inverse-image property for maps that become simplicial homotopy equivalences,
independently of any algebraic structure later used to study those maps.
-/

@[expose] public section

open CategoryTheory

universe v u w v' u'

namespace CategoryTheory.SimplicialObject.Underlying

variable {A : Type u} [Category.{v} A]

/-- The morphism property of simplicial maps that become homotopy equivalences after applying
`U : A ⥤ Type w` degreewise. -/
@[stacks 08P2 "homotopy equivalences detected by an underlying simplicial set"]
def homotopyEquivalences (U : A ⥤ Type w) :
    MorphismProperty (SimplicialObject A) :=
  (SimplicialObject.homotopyEquivalences (Type w)).inverseImage
    ((SimplicialObject.whiskering A (Type w)).obj U)

/-- Membership in `Underlying.homotopyEquivalences U` means that the degreewise image under
`U` is a simplicial homotopy equivalence. -/
@[simp, stacks 08P2 "membership in underlying homotopy equivalences"]
theorem homotopyEquivalences_iff (U : A ⥤ Type w)
    {X Y : SimplicialObject A} (f : X ⟶ Y) :
    homotopyEquivalences U f ↔
      IsHomotopyEquivalence (Functor.whiskerRight f U) := sorry

/-- Detecting homotopy equivalences through a composite functor is the inverse image of the
property detected after the second functor. -/
@[stacks 08P2 "composition of underlying homotopy-equivalence detectors"]
theorem homotopyEquivalences_comp
    {B : Type u'} [Category.{v'} B] (F : A ⥤ B) (U : B ⥤ Type w) :
    homotopyEquivalences (F ⋙ U) =
      (homotopyEquivalences U).inverseImage
        ((SimplicialObject.whiskering A B).obj F) := sorry

end CategoryTheory.SimplicialObject.Underlying
