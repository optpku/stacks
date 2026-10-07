module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/- Lemma 48.17.11 (1) -/
@[stacks 0B6V] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject_isInvertible_of_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left X.obj).toRingedSpace]
    [IsLocalization (Over.left X.obj).toRingedSpace],
    MonoidalCategory.isInvertibleObject (dualizingObject f P A).obj)

/- Lemma 48.17.11 (2) -/
@[stacks 0B6V] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.mapsPerfect_of_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (K : DerivedQCoh.Plus (Over.left Y.obj))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj.obj),
    RingedSpace.ModuleDerived.IsPerfect
      ((upperShriek f P A.plus).obj K).obj.obj)

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
