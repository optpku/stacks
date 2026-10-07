module

public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections of module sheaves on ringed sites

This module provides the unbounded derived global-sections and objectwise-sections functors on
the module category of an arbitrary ringed site.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom

-- Local instance justification (defeq pin): generic total-right-derived APIs must align with the canonical RingedSite.Hom.ModuleDerived presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

namespace ModuleSections

/-- The derived category of modules over the global-sections ring of a ringed site. -/
@[stacks 0D6H "derived category of global-sections modules"]
abbrev Derived (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :=
  DerivedCategory (_root_.ModuleCat.{z} (globalSectionsRing X))

/-- The derived category of modules over the ring of sections at an object of a ringed site. -/
@[stacks 0D6H "derived category of local-section modules"]
abbrev DerivedAt (X : RingedSite.{u, v, w}) (U : X) :=
  DerivedCategory (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op U)))

end ModuleSections

/-- The functor on homotopy categories induced by module-valued global sections. -/
abbrev moduleGlobalSectionsToModuleDerived (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] :=
  @Functor.Homotopy.toDerived
    (ModuleCat.{z} X) inferInstance inferInstance
    (_root_.ModuleCat.{z} (globalSectionsRing X)) inferInstance inferInstance
    (ModuleCat.hasDerivedCategory (globalSectionsRing X))
    (moduleGlobalSectionsFunctor.{z} X)
    (moduleGlobalSectionsFunctor_additive.{z, u, v, w} X)

/-- Module-valued global sections have a canonical unbounded right derived functor when the
source module category is Grothendieck abelian. -/
theorem moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor
    (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    Functor.HasRightDerivedFunctor
      (moduleGlobalSectionsToModuleDerived.{z} X) (ModuleQis.{z} X) := sorry

/-- The unbounded module-valued derived global-sections functor on a ringed site. -/
noncomputable abbrev moduleDerivedGlobalSections (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    ModuleDerived.{z} X ⥤ ModuleSections.Derived.{z} X :=
  @Functor.totalRightDerived
    (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (ModuleSections.Derived.{z} X)
    inferInstance inferInstance inferInstance
    (moduleGlobalSectionsToModuleDerived.{z} X) (moduleLocalization.{z} X)
    (ModuleQis.{z} X) inferInstance
    (moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor X)

/-- The functor on homotopy categories induced by additive global sections on module sheaves. -/
abbrev moduleGlobalSectionsToDerived (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :=
  @Functor.Homotopy.toDerived
    (ModuleCat.{z} X) inferInstance inferInstance
    AddCommGrpCat.{z} inferInstance inferInstance AddCommGrpCat.hasDerivedCategory
    (moduleGlobalSectionsAdditiveFunctor.{z} X)
    (moduleGlobalSectionsAdditiveFunctor_additive.{z, u, v, w} X)

/-- Additive global sections have a canonical unbounded right derived functor when the source
module category is Grothendieck abelian. -/
theorem moduleGlobalSectionsToDerived_hasRightDerivedFunctor (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    Functor.HasRightDerivedFunctor
      (moduleGlobalSectionsToDerived.{z} X) (ModuleQis.{z} X) := sorry

/-- The unbounded right derived global-sections functor on module sheaves. -/
@[stacks 0D6H "derived global sections"]
noncomputable abbrev moduleGlobalSectionsDerived (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  @Functor.totalRightDerived
    (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (DerivedCategory AddCommGrpCat.{z})
    inferInstance inferInstance inferInstance
    (moduleGlobalSectionsToDerived.{z} X) (moduleLocalization.{z} X)
    (ModuleQis.{z} X) inferInstance
    (moduleGlobalSectionsToDerived_hasRightDerivedFunctor X)

/-- Evaluation of a module sheaf at a fixed object of a ringed site is additive. -/
theorem moduleSectionsEvaluation_additive (X : RingedSite.{u, v, w}) (U : X) :
    (SheafOfModules.evaluation.{z} X.structureSheaf (op U)).Additive := sorry

/-- The functor on homotopy categories induced by sections over a fixed object. -/
abbrev moduleSectionsToDerived (X : RingedSite.{u, v, w}) (U : X) :
    HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleSections.DerivedAt.{z} X U :=
  @Functor.Homotopy.toDerived
    (ModuleCat.{z} X) inferInstance inferInstance
    (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op U))) inferInstance inferInstance
    (ModuleCat.hasDerivedCategory (X.structureSheaf.obj.obj (op U)))
    (SheafOfModules.evaluation.{z} X.structureSheaf (op U))
    (moduleSectionsEvaluation_additive X U)

/-- The objectwise sections functor admits an unbounded right derived functor. -/
theorem moduleSectionsToDerived_hasRightDerivedFunctor (X : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}] [IsGrothendieckAbelian (ModuleCat.{z} X)] (U : X) :
    Functor.HasRightDerivedFunctor
      (moduleSectionsToDerived.{z} X U) (ModuleQis.{z} X) := sorry

/-- The unbounded right derived sections functor `RΓ(U, -)` on module sheaves. -/
@[stacks 0D6H "derived sections over an object"]
noncomputable abbrev moduleSectionsDerived (X : RingedSite.{u, v, w}) (U : X)
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    ModuleDerived.{z} X ⥤ ModuleSections.DerivedAt.{z} X U :=
  @Functor.totalRightDerived
    (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (ModuleSections.DerivedAt.{z} X U)
    inferInstance inferInstance inferInstance
    (moduleSectionsToDerived.{z} X U) (moduleLocalization.{z} X)
    (ModuleQis.{z} X) inferInstance
    (moduleSectionsToDerived_hasRightDerivedFunctor X U)

end RingedSite.Hom

namespace RingedSiteDerivedSections

/-- Scoped notation for the unbounded derived global-sections functor on a ringed site. -/
scoped macro:max "RΓ[" X:term "]" : term =>
  `(RingedSite.Hom.moduleGlobalSectionsDerived $X)

@[inherit_doc RingedSite.Hom.moduleSectionsDerived]
scoped notation3:max "RΓ[" X "](" U ")" =>
  RingedSite.Hom.moduleSectionsDerived X U

end RingedSiteDerivedSections

-- These derived functors are the canonical total right derived constructions of the localization
-- functors above.
