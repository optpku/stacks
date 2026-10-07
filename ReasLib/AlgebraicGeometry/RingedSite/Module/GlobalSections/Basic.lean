module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued global sections on ringed sites

This module constructs the global-sections ring of an arbitrary ringed site and the corresponding
module-valued global-sections functor.  Derived global sections are kept in the sibling
`Derived` module.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom

/-- The ring `Γ(𝒞, 𝒪_X)` of global sections of the structure sheaf of a ringed site. -/
@[stacks 0D6H "global-sections ring"]
abbrev globalSectionsRing (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] : RingCat.{w} :=
  limit X.structureSheaf.obj

/-- The constant presheaf on the global-sections ring of a ringed site. -/
abbrev globalSectionsRingPresheaf (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    Xᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Xᵒᵖ).obj (globalSectionsRing X)

/-- Evaluation of a global section gives a morphism from the constant global-sections presheaf
to the structure sheaf. -/
abbrev globalSectionsRingHom (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    globalSectionsRingPresheaf X ⟶ X.structureSheaf.obj :=
  (limit.cone X.structureSheaf.obj).π

/-- Restricting scalars along `globalSectionsRingHom` turns module sheaves into presheaves of
modules over the constant global-sections ring. -/
abbrev moduleGlobalSectionsPresheaf (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    ModuleCat.{z} X ⥤ PresheafOfModules.{z} (globalSectionsRingPresheaf X) :=
  SheafOfModules.forget X.structureSheaf ⋙
    PresheafOfModules.restrictScalars (globalSectionsRingHom X)

/-- The diagram of local sections of a module sheaf, regarded as modules over the global-sections
ring. -/
abbrev moduleGlobalSectionsDiagram (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    (ℱ : ModuleCat.{z} X) :
    Xᵒᵖ ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) := by
  refine
    { obj := fun U ↦ ((moduleGlobalSectionsPresheaf X).obj ℱ).obj U
      map := fun f ↦ ((moduleGlobalSectionsPresheaf X).obj ℱ).map f
      map_id := ?_
      map_comp := ?_ }
  all_goals sorry

/-- A morphism of module sheaves induces the objectwise morphism between their diagrams of
sections over the global-sections ring. -/
noncomputable def moduleGlobalSectionsDiagramMap
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    {ℱ 𝒢 : ModuleCat.{z} X} (f : ℱ ⟶ 𝒢) :
    moduleGlobalSectionsDiagram X ℱ ⟶ moduleGlobalSectionsDiagram X 𝒢 where
  app U := ((moduleGlobalSectionsPresheaf X).map f).app U
  naturality := sorry

/-- Module sheaves map functorially to their diagrams of local sections over the global-sections
ring. -/
noncomputable def moduleGlobalSectionsDiagramFunctor
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    ModuleCat.{z} X ⥤ Xᵒᵖ ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) := by
  refine
    { obj := moduleGlobalSectionsDiagram X
      map := moduleGlobalSectionsDiagramMap X
      map_id := ?_
      map_comp := ?_ }
  all_goals sorry

/-- The category of modules over the global-sections ring has limits indexed by the site whenever
the module universe contains the site-object universe. -/
theorem moduleGlobalSectionsHasLimitsOfShape
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] [UnivLE.{u, z}] :
    HasLimitsOfShape Xᵒᵖ (_root_.ModuleCat.{z} (globalSectionsRing X)) :=
  _root_.ModuleCat.hasLimitsOfShape

/-- The module of compatible global sections of a module sheaf on a ringed site. -/
abbrev moduleGlobalSectionsObject (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] (ℱ : ModuleCat.{z} X) :
    _root_.ModuleCat.{z} (globalSectionsRing X) :=
  @limit _ _ _ _ (moduleGlobalSectionsDiagram X ℱ)
    (@HasLimitsOfShape.has_limit _ _ _ _
      (moduleGlobalSectionsHasLimitsOfShape X) (moduleGlobalSectionsDiagram X ℱ))

/-- The `Γ(𝒞, 𝒪_X)`-module-valued global-sections functor on `𝒪_X`-modules. -/
@[stacks 0D6H "module-valued global sections"]
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] :
    ModuleCat.{z} X ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) :=
  moduleGlobalSectionsDiagramFunctor X ⋙
    @lim _ _ _ _ (moduleGlobalSectionsHasLimitsOfShape X)

/-- The additive global-sections functor on `𝒪_X`-modules, computed after forgetting to
abelian sheaves. -/
@[stacks 0D6H "additive global sections"]
abbrev moduleGlobalSectionsAdditiveFunctor (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    ModuleCat.{z} X ⥤ AddCommGrpCat.{z} :=
  SheafOfModules.toSheaf.{z} X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{z}

/-- Forgetting the `Γ(𝒞, 𝒪_X)`-module structure on global sections recovers the additive
global-sections functor. -/
theorem moduleGlobalSectionsForget_eq (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    moduleGlobalSectionsFunctor.{z} X ⋙
        forget₂ (_root_.ModuleCat.{z} (globalSectionsRing X)) AddCommGrpCat.{z} =
      moduleGlobalSectionsAdditiveFunctor.{z} X := sorry

end RingedSite.Hom
