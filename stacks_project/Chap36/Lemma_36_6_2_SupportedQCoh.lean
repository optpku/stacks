/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

#check
  (quasiCoherentOnSupport :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X),
      ObjectProperty
        (SheafOfModules.ClosedSubset.SupportedDerived X.toRingedSpace.ringCatSheaf T))

#check
  (SupportedOn :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X), Type (u + 1))

namespace SupportedOn

#check
  (inclusion_mapsTo :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X),
      quasiCoherentOnSupport X T ≤
        (derivedQuasiCoherentModuleProperty X).inverseImage
          (SheafOfModules.ClosedSubset.SupportedDerived.inclusion
            X.toRingedSpace.ringCatSheaf T))

#check
  (inclusion :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X),
      SupportedOn X T ⥤ Scheme.DerivedQCoh X)

#check
  (coreflector_mapsTo :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      derivedQuasiCoherentModuleProperty X ≤
        (quasiCoherentOnSupport X T).inverseImage
          (SheafOfModules.ClosedSubset.SupportedDerived.coreflector
            X.toRingedSpace.ringCatSheaf T))

#check
  (coreflector :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      Scheme.DerivedQCoh X ⥤ SupportedOn X T)

#check
  (inclusionCompιIso :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X),
      inclusion X T ⋙ Scheme.DerivedQCoh.inclusion X ≅
        (quasiCoherentOnSupport X T).ι ⋙
          SheafOfModules.ClosedSubset.SupportedDerived.inclusion
            X.toRingedSpace.ringCatSheaf T)

#check
  (coreflectorCompιIso :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      coreflector X T hT ⋙ (quasiCoherentOnSupport X T).ι ≅
        Scheme.DerivedQCoh.inclusion X ⋙
          SheafOfModules.ClosedSubset.SupportedDerived.coreflector
            X.toRingedSpace.ringCatSheaf T)

#check
  (obj_properties :
    ∀ {X : Scheme.{u}} {T : TopologicalSpace.Closeds X} (K : SupportedOn X T),
      derivedQuasiCoherentModuleProperty X K.obj.obj ∧
        RingedSpace.ModuleDerived.IsSupportedOn K.obj.obj (T : Set X))

#check
  (adjunction :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      inclusion X T ⊣ coreflector X T hT)

end SupportedOn

end AlgebraicGeometry.Scheme.DerivedQCoh
