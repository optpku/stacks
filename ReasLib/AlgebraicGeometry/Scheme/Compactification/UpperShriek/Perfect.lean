/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Homothety
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/-- For a perfect morphism of finite-type separated schemes over a Noetherian base,
the upper-shriek dualizing object has bounded coherent cohomology. -/
theorem dualizingObject_boundedCoherent_of_perfect
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    ((t.bounded : ObjectProperty
        (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)) ⊓
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))
      (dualizingObject f P A).obj := sorry

/-- For a perfect morphism of finite-type separated schemes, the upper-shriek
dualizing object has locally finite Tor dimension over the target. -/
theorem dualizingObject_locallyHasFiniteTorDimension_of_perfect
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).restrict U.isOpenEmbedding))]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
      (X := RingedSpace.Hom.inverseImageBase f.hom.left.toShHom)
      ((RingedSpace.ModuleDerived.relativeRestriction
          (Over.Hom.left f.hom).toShHom).obj
        (dualizingObject f P A).obj) := sorry

/-- For a perfect morphism, the canonical homothety of the upper-shriek
dualizing object is an isomorphism. -/
@[instance]
theorem dualizingHomothety_isIso_of_perfect
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left X.obj).toRingedSpace]
    [IsLocalization (Over.left X.obj).toRingedSpace]
    (H_X : MonoidalClosed
      (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)) :
    IsIso (dualizingHomothety f P A H_X) := sorry

/-- For a perfect morphism, upper shriek sends bounded coherent complexes to
bounded coherent complexes. -/
theorem mapsBoundedCoherent_of_perfect
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsPerfectRingMap f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (K : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf])
    (hK : (t.bounded : ObjectProperty
      (RingedSpace.ModuleDerived (Over.left Y.obj).toRingedSpace)) K.obj.obj) :
    ((t.bounded : ObjectProperty
        (RingedSpace.ModuleDerived (Over.left X.obj).toRingedSpace)) ⊓
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))
      ((upperShriek f P A.plus).obj
        ((DerivedQCoh.coherentPlusInclusion (Over.left Y.obj)).obj K)).obj.obj := sorry

/-- For a perfect morphism and a bounded-below quasicoherent complex, the
projection-formula tensor comparison for upper shriek is an isomorphism. -/
@[instance]
theorem tensorNatTransPlus_app_isIso_of_perfect
    {S : Scheme.{u}} [IsNoetherian S]
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
    (K : DerivedQCoh.Plus (Over.left Y.obj)) :
    IsIso ((tensorNatTransPlus f P A).app K) := sorry

/-- For a local complete-intersection morphism of finite-type separated schemes over a
Noetherian base, the upper-shriek dualizing object of the structure sheaf is invertible. -/
@[instance]
theorem dualizingObject_isInvertible_of_isLocalCompleteIntersection
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (Over.left X.obj).toRingedSpace]
    [TensorDescends (Over.left X.obj).toRingedSpace]
    [IsLocalization (Over.left X.obj).toRingedSpace] :
    MonoidalCategory.isInvertibleObject (dualizingObject f P A).obj := sorry

/-- For a local complete-intersection morphism of finite-type separated schemes, the
upper-shriek functor sends perfect complexes to perfect complexes. -/
theorem mapsPerfect_of_isLocalCompleteIntersection
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left]
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (K : DerivedQCoh.Plus (Over.left Y.obj))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj.obj) :
    RingedSpace.ModuleDerived.IsPerfect
      ((upperShriek f P A.plus).obj K).obj.obj := sorry

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
