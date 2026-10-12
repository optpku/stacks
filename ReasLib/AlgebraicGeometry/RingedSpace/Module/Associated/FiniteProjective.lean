/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Free
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite projective modules and associated module sheaves

Associated sheaves carry finite projective modules to retracts of finite free module sheaves.
For the identity map on the global-sections ring, this restriction is adjoint to global sections
and gives an equivalence of the corresponding full subcategories.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective

/-- Associated sheaves of finite projective modules are retracts of finite free module sheaves. -/
@[stacks 0FPF "associated sheaf of a finite projective module"]
theorem obj_mem {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (alpha : R →+* X.globalSectionsRing) {M : ModuleCat.{u} R}
    (hM : ModuleCat.finiteProjective R M) :
    SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf
      (Associated.obj alpha M) := sorry

/-- The identity-scalar associated functor maps finite projective modules to finite-free
retracts. -/
theorem associated_mapsTo (X : RingedSpace.{u}) :
    ModuleCat.finiteProjective X.globalSectionsRing ≤
      (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).inverseImage
        (Associated.functor (RingHom.id X.globalSectionsRing)) := sorry

/-- Global sections of a finite-free-retract module sheaf form a finite projective module. -/
@[stacks 0FPF "global sections of a finite-free retract"]
theorem globalSections_obj_mem (X : RingedSpace.{u}) {F : X.Modules}
    (hF : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf F) :
    ModuleCat.finiteProjective X.globalSectionsRing
      (X.moduleGlobalSectionsFunctor.obj F) := sorry

/-- Global sections map finite-free retracts to finite projective modules. -/
theorem globalSections_mapsTo (X : RingedSpace.{u}) :
    SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf ≤
      (ModuleCat.finiteProjective X.globalSectionsRing).inverseImage
        X.moduleGlobalSectionsFunctor := sorry

/-- The associated-module functor restricted to finite projective modules. -/
@[stacks 0FPF "restricted associated functor"]
noncomputable def associated (X : RingedSpace.{u}) :
    ModuleCat.FiniteProjective.{u, u} X.globalSectionsRing ⥤
      (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (Associated.functor (RingHom.id X.globalSectionsRing)) (associated_mapsTo X)

/-- The global-sections functor restricted to finite-free-retract module sheaves. -/
@[stacks 0FPF "restricted global-sections functor"]
noncomputable def globalSections (X : RingedSpace.{u}) :
    (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory ⥤
      ModuleCat.FiniteProjective.{u, u} X.globalSectionsRing :=
  ObjectProperty.FullSubcategory.restrict X.moduleGlobalSectionsFunctor
    (globalSections_mapsTo X)

/-- Forgetting the restricted associated functor recovers the ambient associated functor. -/
noncomputable def associatedCompιIso (X : RingedSpace.{u}) :
    associated X ⋙
        (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ≅
      (ModuleCat.finiteProjective X.globalSectionsRing).ι ⋙
        Associated.functor (RingHom.id X.globalSectionsRing) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (P := ModuleCat.finiteProjective X.globalSectionsRing)
    (Q := SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf)
    (Associated.functor (RingHom.id X.globalSectionsRing)) (associated_mapsTo X)

/-- Forgetting restricted global sections recovers the ambient global-sections functor. -/
noncomputable def globalSectionsCompιIso (X : RingedSpace.{u}) :
    globalSections X ⋙ (ModuleCat.finiteProjective X.globalSectionsRing).ι ≅
      (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙
        X.moduleGlobalSectionsFunctor :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (P := SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf)
    (Q := ModuleCat.finiteProjective X.globalSectionsRing)
    X.moduleGlobalSectionsFunctor (globalSections_mapsTo X)

/-- The associated/global-sections adjunction restricted to finite projectives and finite-free
retracts. -/
@[stacks 0FPF "restricted adjunction"]
noncomputable def adjunction (X : RingedSpace.{u}) :
    associated X ⊣ globalSections X :=
  (Associated.idAdjunction X).restrictFullyFaithful
    (ModuleCat.finiteProjective X.globalSectionsRing).fullyFaithfulι
    (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).fullyFaithfulι
    (associatedCompιIso X).symm (globalSectionsCompιIso X).symm

/-- The unit of the restricted associated/global-sections adjunction is invertible. -/
instance unit_isIso (X : RingedSpace.{u})
    (P : ModuleCat.FiniteProjective.{u, u} X.globalSectionsRing) :
    IsIso ((adjunction X).unit.app P) := sorry

/-- The counit of the restricted associated/global-sections adjunction is invertible. -/
instance counit_isIso (X : RingedSpace.{u})
    (F : (SheafOfModules.finiteFreeRetractModuleProperty
      X.ringCatSheaf).FullSubcategory) :
    IsIso ((adjunction X).counit.app F) := sorry

/-- Global sections and associated sheaves give an explicit equivalence between finite-free
retract module sheaves and finite projective modules. -/
@[stacks 0FPF "equivalence"]
noncomputable def equivalence (X : RingedSpace.{u}) :
    (SheafOfModules.finiteFreeRetractModuleProperty
      X.ringCatSheaf).FullSubcategory ≌
      ModuleCat.FiniteProjective.{u, u} X.globalSectionsRing :=
  (adjunction X).toEquivalence.symm

/-- Lemma 20.52.1 (0FPF): restricted global sections are an equivalence. -/
@[stacks 0FPF]
instance globalSections_isEquivalence (X : RingedSpace.{u}) :
    (globalSections X).IsEquivalence := sorry

/-- The restricted associated-module functor is an equivalence. -/
instance associated_isEquivalence (X : RingedSpace.{u}) :
    (associated X).IsEquivalence := sorry

end AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective
