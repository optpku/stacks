module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Coextension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open RingedSpace.ModuleDerived.KFlat
open SheafOfModules.RingedSite.DerivedCoextension

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- For an affine morphism, derived coextension followed by derived restriction is
isomorphic to the internal-Hom functor from the pushed-forward structure sheaf. -/
theorem derivedRestrictionCoextension_isomorphic_internalHom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) :
    IsIsomorphic
      (functor.{u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) ⋙
        restriction.{u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))
      (MonoidalClosed.ihomOf H
        ((DerivedCategory.singleFunctor.{u + 1, u, u + 1} X.Modules 0).obj
          ((RingedSpace.Hom.pushforward f.toShHom).obj
            (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf)))) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
