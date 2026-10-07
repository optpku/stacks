module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

/-!
# Coherent cohomology of derived internal Hom

This file records coherent-cohomology and boundedness preservation for derived internal Hom on
locally Noetherian schemes.
-/

open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- On a locally Noetherian scheme, derived internal Hom from an object with bounded-above
coherent cohomology to an object with bounded-below coherent cohomology has bounded-below
coherent cohomology. -/
theorem boundedBelowCoherentCohomology {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K L : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
        ((ihomOf H K).obj L) ∧
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
        ((ihomOf H K).obj L) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
