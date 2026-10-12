/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedSubset
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Quasi-coherence of the underlying ambient derived module of a supported object. -/
def quasiCoherentOnSupport (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    ObjectProperty
      (SheafOfModules.ClosedSubset.SupportedDerived X.toRingedSpace.ringCatSheaf T) :=
  (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
    (SheafOfModules.ClosedSubset.SupportedDerived.inclusion X.toRingedSpace.ringCatSheaf T)

/-- The category of derived `𝒪_X`-modules with quasi-coherent cohomology supported on `T`. -/
abbrev SupportedOn (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :=
  (quasiCoherentOnSupport X T).FullSubcategory

namespace SupportedOn

/-- The ambient supported-derived inclusion preserves quasi-coherent cohomology. -/
theorem inclusion_mapsTo (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    quasiCoherentOnSupport X T ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
          (SheafOfModules.ClosedSubset.SupportedDerived.inclusion
            X.toRingedSpace.ringCatSheaf T) := sorry

/-- The inclusion of supported derived modules with quasi-coherent cohomology into all derived
modules with quasi-coherent cohomology. -/
noncomputable def inclusion (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    SupportedOn X T ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  FullSubcategory.restrict
    (SheafOfModules.ClosedSubset.SupportedDerived.inclusion X.toRingedSpace.ringCatSheaf T)
    (inclusion_mapsTo X T)

/-- If the complement of `T` is retrocompact, the ambient closed-support coreflector preserves
quasi-coherent cohomology. -/
theorem coreflector_mapsTo (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
    (hT : IsRetrocompact ((T : Set X)ᶜ)) :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (quasiCoherentOnSupport X T).inverseImage
        (SheafOfModules.ClosedSubset.SupportedDerived.coreflector
          X.toRingedSpace.ringCatSheaf T) := sorry

/-- The closed-support coreflector restricted to derived modules with quasi-coherent
cohomology. -/
noncomputable def coreflector (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
    (hT : IsRetrocompact ((T : Set X)ᶜ)) :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      SupportedOn X T :=
  FullSubcategory.restrict
    (SheafOfModules.ClosedSubset.SupportedDerived.coreflector X.toRingedSpace.ringCatSheaf T)
    (coreflector_mapsTo X T hT)

/-- Forgetting the restricted inclusion recovers the ambient supported-derived inclusion. -/
noncomputable def inclusionCompιIso (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    inclusion X T ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ≅
      (quasiCoherentOnSupport X T).ι ⋙
        SheafOfModules.ClosedSubset.SupportedDerived.inclusion
          X.toRingedSpace.ringCatSheaf T :=
  FullSubcategory.restrict.compιIso
    (SheafOfModules.ClosedSubset.SupportedDerived.inclusion X.toRingedSpace.ringCatSheaf T)
    (inclusion_mapsTo X T)

/-- Forgetting the restricted coreflector recovers the ambient closed-support coreflector. -/
noncomputable def coreflectorCompιIso (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
    (hT : IsRetrocompact ((T : Set X)ᶜ)) :
    coreflector X T hT ⋙ (quasiCoherentOnSupport X T).ι ≅
      (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
        SheafOfModules.ClosedSubset.SupportedDerived.coreflector
          X.toRingedSpace.ringCatSheaf T :=
  FullSubcategory.restrict.compιIso
    (SheafOfModules.ClosedSubset.SupportedDerived.coreflector X.toRingedSpace.ringCatSheaf T)
    (coreflector_mapsTo X T hT)

/-- An object supported on `T` has quasi-coherent cohomology and cohomology supported on `T`. -/
theorem obj_properties {X : Scheme.{u}} {T : TopologicalSpace.Closeds X}
    (K : SupportedOn X T) :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K.obj.obj ∧
      RingedSpace.ModuleDerived.IsSupportedOn K.obj.obj (T : Set X) := sorry

/-- The restricted closed-support coreflector is right adjoint to the inclusion. -/
noncomputable def adjunction (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
    (hT : IsRetrocompact ((T : Set X)ᶜ)) :
    inclusion X T ⊣ coreflector X T hT :=
  FullSubcategory.adjunction
    (SheafOfModules.ClosedSubset.SupportedDerived.inclusion X.toRingedSpace.ringCatSheaf T)
    (SheafOfModules.ClosedSubset.SupportedDerived.coreflector X.toRingedSpace.ringCatSheaf T)
    (SheafOfModules.ClosedSubset.SupportedDerived.adjunction X.toRingedSpace.ringCatSheaf T)
    (inclusion_mapsTo X T) (coreflector_mapsTo X T hT)

end SupportedOn

end AlgebraicGeometry.Scheme.DerivedQCoh

end
