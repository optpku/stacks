module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Underlying additive derived sections

This module owns the additive-sheaf models used when a module-valued section functor is compared
with its underlying abelian functor.  The source-facing names are grouped under
`RingedSite.Hom.ModuleSections`; no chapter implementation is imported.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w})

namespace Underlying

/-- The homotopy-to-derived additive sections functor over `U`. -/
@[stacks 0D6J "underlying additive sections on homotopy categories"]
abbrev sectionsToDerived (U : X) :
    HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  Functor.Homotopy.toDerived (sections X U)

end Underlying

/-- Finite limits are preserved by the section-module forgetful functor at the fixed coefficient
universe used by the derived section API. -/
@[stacks 0D6J "section-module forgetful finite limits"]
noncomputable instance sectionForget_preservesFiniteLimits (U : X) :
    PreservesFiniteLimits (sectionForget.{z} X U) := sorry

/-- Finite colimits are preserved by the section-module forgetful functor at the fixed coefficient
universe used by the derived section API. -/
@[stacks 0D6J "section-module forgetful finite colimits"]
noncomputable instance sectionForget_preservesFiniteColimits (U : X) :
    PreservesFiniteColimits (sectionForget.{z} X U) := sorry

namespace Underlying

/-- The additive sections functor admits its canonical right-derived-functor witness. -/
@[stacks 0D6J "underlying additive sections right-derived model"]
instance sectionsToDerived_hasRightDerivedFunctor
    [UnivLE.{max u v, z}] [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)] (U : X) :
    Functor.HasRightDerivedFunctor
      (sectionsToDerived.{z} X U) (ModuleQis.{z} X) := sorry

/-- The total right-derived additive sections functor over `U`. -/
@[stacks 0D6J "underlying additive derived sections"]
noncomputable abbrev sectionsDerived (U : X)
    [UnivLE.{max u v, z}]
    [Functor.HasRightDerivedFunctor
      (sectionsToDerived.{z} X U) (ModuleQis.{z} X)] :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  @Functor.totalRightDerived
    (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (DerivedCategory AddCommGrpCat.{z})
    inferInstance inferInstance inferInstance
    (sectionsToDerived.{z} X U) (moduleLocalization.{z} X)
    (ModuleQis.{z} X) inferInstance
    inferInstance

/-- The homotopy-to-derived global sections functor on additive sheaves. -/
@[stacks 0D6J "additive sheaf global sections on homotopy categories"]
abbrev globalToDerived
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  Functor.Homotopy.toDerived (Sheaf.Γ X.siteTopology AddCommGrpCat.{z})

/-- Additive sheaf global sections admit a canonical right-derived-functor witness. -/
@[stacks 0D6J "additive sheaf global sections right-derived model"]
instance globalToDerived_hasRightDerivedFunctor
    [HasSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
    [IsGrothendieckAbelian (Sheaf X.siteTopology AddCommGrpCat.{z})] :
    Functor.HasRightDerivedFunctor (globalToDerived X)
      (HomotopyCategory.quasiIso
        (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The total right-derived global sections functor on additive sheaves. -/
@[stacks 0D6J "additive sheaf derived global sections"]
noncomputable abbrev globalDerived
    [HasSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
    [Functor.HasRightDerivedFunctor (globalToDerived X)
      (HomotopyCategory.quasiIso
        (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))] :
    DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  Functor.totalRightDerived (globalToDerived X)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
        DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
    (HomotopyCategory.quasiIso
      (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))

/-- The module global-sections homotopy functor and the underlying additive model are canonically
identified. -/
@[stacks 0D6J "global sections underlying bridge"]
noncomputable def globalCompIso
    [UnivLE.{max u v, z}]
    [HasSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    moduleGlobalSectionsToDerived.{z} X ≅
      (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
        globalToDerived X :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (underlyingAbelianSheafFunctor.{z} X ⋙
            Sheaf.Γ X.siteTopology AddCommGrpCat.{z})) (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).symm ≪≫
    (Functor.associator
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((Sheaf.Γ X.siteTopology AddCommGrpCat.{z}).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z}))

/-- The homotopy-to-derived objectwise sections functor is identified with module sections followed
by the derived forgetful functor on the section module category. -/
@[stacks 0D6J "objectwise derived sections underlying bridge"]
noncomputable def sectionsCompIso (U : X)
    [UnivLE.{max u v, z}] :
    sectionsToDerived X U ≅
      moduleSectionsToDerived.{z} X U ⋙
      (sectionForget.{z} X U).mapDerivedCategory :=
  letI :
      (SheafOfModules.evaluation.{z} X.structureSheaf (op U)).Additive :=
    moduleSectionsEvaluation_additive X U
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (sectionsForgetIso X U)) ≪≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl
            (SheafOfModules.evaluation.{z} X.structureSheaf (op U) ⋙
              sectionForget.{z} X U)) (up ℤ)).symm)
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z}) ≪≫
    (Functor.associator
      ((SheafOfModules.evaluation.{z} X.structureSheaf (op U)).mapHomotopyCategory
        (up ℤ))
      ((sectionForget.{z} X U).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory AddCommGrpCat.{z} (up ℤ) ⥤
          DerivedCategory AddCommGrpCat.{z})).symm ≪≫
    Functor.isoWhiskerLeft
      ((SheafOfModules.evaluation.{z} X.structureSheaf (op U)).mapHomotopyCategory (up ℤ))
      ((@Functor.mapDerivedCategoryFactorsh
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op U)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (X.structureSheaf.obj.obj (op U)))
        AddCommGrpCat.{z} inferInstance inferInstance AddCommGrpCat.hasDerivedCategory
        (sectionForget.{z} X U) inferInstance inferInstance inferInstance).symm) ≪≫
    (Functor.associator
      ((SheafOfModules.evaluation.{z} X.structureSheaf (op U)).mapHomotopyCategory
        (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (X.structureSheaf.1.obj (op U))) (up ℤ) ⥤
          DerivedCategory (_root_.ModuleCat.{z} (X.structureSheaf.1.obj (op U))))
      (sectionForget.{z} X U).mapDerivedCategory).symm

end Underlying

end RingedSite.Hom.ModuleSections
