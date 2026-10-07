module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/- Lemma 48.17.9 (1) -/
@[stacks 0B6U] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject_boundedCoherent_of_perfect :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)),
    ((t.bounded : ObjectProperty
        (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)) ⊓
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))
      (dualizingObject f P A).obj)

/- Lemma 48.17.9 (2) -/
@[stacks 0B6U] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject_locallyHasFiniteTorDimension_of_perfect :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)),
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction
          (Over.Hom.left f.hom).toShHom).obj
        (dualizingObject f P A).obj))

/- Lemma 48.17.9 (3) -/
@[stacks 0B6U] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingHomothety_isIso_of_perfect :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left X.obj).toRingedSpace]
    [IsLocalization (Over.left X.obj).toRingedSpace]
    (H_X : MonoidalClosed
      (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)),
    IsIso (dualizingHomothety f P A H_X))

/- Lemma 48.17.9 (4) -/
@[stacks 0B6U] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.mapsBoundedCoherent_of_perfect :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (K : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (hK : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Over.left Y.obj).toRingedSpace)) K.obj.obj),
    ((t.bounded : ObjectProperty
        (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)) ⊓
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))
      ((upperShriek f P A.plus).obj
        ((DerivedQCoh.coherentPlusInclusion (Over.left Y.obj)).obj K)).obj.obj)

/- Lemma 48.17.9 (5) -/
@[stacks 0B6U] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.tensorNatTransPlus_app_isIso_of_perfect :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left X.obj).toRingedSpace]
    [IsLocalization (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left (Over.mk (Over.Hom.left f.hom))).toRingedSpace]
    [IsLocalization (Over.left (Over.mk (Over.Hom.left f.hom))).toRingedSpace]
    [HomotopyTensorDescends (Over.left Y.obj).toRingedSpace]
    [TensorDescends (Over.left Y.obj).toRingedSpace]
    [IsLocalization (Over.left Y.obj).toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Over.left Y.obj).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Over.left Y.obj).toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived
        (Over.left (Over.mk (Over.Hom.left f.hom))).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.left (Over.mk (Over.Hom.left f.hom))).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)]
    (K : DerivedQCoh.Plus (Over.left Y.obj)),
    IsIso ((tensorNatTransPlus f P A).app K))

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
