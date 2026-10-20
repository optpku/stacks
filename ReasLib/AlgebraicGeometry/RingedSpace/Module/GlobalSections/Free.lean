/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Module.FiniteFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

/-!
# Global sections of free module sheaves

This leaf identifies global sections of a free module sheaf with the corresponding free module
over the global-sections ring whenever global sections preserve the relevant coproduct. The
`Finsupp` form is valid for an arbitrary basis; the ordinary function form is its finite-basis
specialization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Evaluating the unit module sheaf on the top open gives the regular module over
`Γ(X, 𝒪_X)`. -/
noncomputable def moduleGlobalSectionsUnitIso (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅
      ModuleCat.of (globalSectionsRing X) (globalSectionsRing X) :=
  Iso.refl _

/-- If global sections preserve the `I`-indexed coproduct of unit modules, then global sections
of the free `𝒪_X`-module on `I` are the finitely supported free `Γ(X, 𝒪_X)`-module on `I`. -/
noncomputable def moduleGlobalSectionsFreeIsoFinsupp
    (X : RingedSpace.{u}) (I : Type u)
    [PreservesColimit
      (Discrete.functor fun _ : I ↦ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
      (moduleGlobalSectionsFunctor X)] :
    (moduleGlobalSectionsFunctor X).obj
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ≅
      ModuleCat.of (globalSectionsRing X) (I →₀ globalSectionsRing X) :=
  (isColimitOfPreserves (moduleGlobalSectionsFunctor X)
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)).coconePointsIsoOfEquivalence
    (ModuleCat.finsuppCoconeIsColimit (globalSectionsRing X) (globalSectionsRing X) I)
    CategoryTheory.Equivalence.refl
    (Discrete.natIso fun _ ↦ moduleGlobalSectionsUnitIso X).symm

/-- Under `moduleGlobalSectionsFreeIsoFinsupp`, the global section associated to the `i`th free
generator is the `i`th finitely supported basis vector. -/
@[simp]
theorem moduleGlobalSectionsFreeIsoFinsupp_hom_freeSection
    (X : RingedSpace.{u}) (I : Type u)
    [PreservesColimit
      (Discrete.functor fun _ : I ↦ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
      (moduleGlobalSectionsFunctor X)]
    (i : I) :
    (moduleGlobalSectionsFreeIsoFinsupp X I).hom
        (sectionsEquivTop
          (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)
          (SheafOfModules.freeSection (R := X.ringCatSheaf) i)) =
      Finsupp.single i 1 := sorry

/-- If module-valued global sections are additive, then on a finite basis they identify the free
`𝒪_X`-module on `I` with the ordinary function-model free `Γ(X, 𝒪_X)`-module
`I → Γ(X, 𝒪_X)`. -/
noncomputable def moduleGlobalSectionsFreeIsoPi
    (X : RingedSpace.{u}) (I : Type u) [Finite I]
    [(moduleGlobalSectionsFunctor X).Additive] :
    (moduleGlobalSectionsFunctor X).obj
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ≅
      ModuleCat.of (globalSectionsRing X) (I → globalSectionsRing X) :=
  moduleGlobalSectionsFreeIsoFinsupp X I ≪≫
    ModuleCat.finsuppToFunIso (R := globalSectionsRing X) (I := I)

/-- Under `moduleGlobalSectionsFreeIsoPi`, the global section associated to the `i`th free
generator has Kronecker-delta coordinate `j`. -/
@[simp]
theorem moduleGlobalSectionsFreeIsoPi_hom_freeSection_apply
    (X : RingedSpace.{u}) (I : Type u) [Finite I]
    [(moduleGlobalSectionsFunctor X).Additive]
    (i j : I) :
    ((moduleGlobalSectionsFreeIsoPi X I).hom
        (sectionsEquivTop
          (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)
          (SheafOfModules.freeSection (R := X.ringCatSheaf) i))) j =
      (Finsupp.single i 1 : I →₀ globalSectionsRing X) j := sorry

end AlgebraicGeometry.RingedSpace
