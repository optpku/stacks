/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic

/-!
# Computation rules for module global sections on ringed sites

These rules expose evaluation, restriction, and functoriality without requiring downstream files
to unfold the compatible-sections submodule used by the global-sections construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom

namespace ModuleSections

/-- Evaluation of the global-sections ring at an object is the corresponding limit projection. -/
@[stacks 0D6H "global-sections evaluation", simp]
theorem ringHom_app (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] (U : Xᵒᵖ) :
    (globalSectionsRingHom X).app U = limit.π X.structureSheaf.obj U := sorry

/-- Evaluation of a global section is computed by the corresponding limit projection. -/
@[simp]
theorem ringHom_app_apply (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] (U : Xᵒᵖ)
    (s : globalSectionsRing X) :
    ((globalSectionsRingHom X).app U).hom s =
      (limit.π X.structureSheaf.obj U).hom s := sorry

/-- The evaluation of a global section commutes with restriction along a morphism of the site. -/
@[simp]
theorem ringHom_naturality_apply (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    {U V : Xᵒᵖ} (f : U ⟶ V) (s : globalSectionsRing X) :
    (X.structureSheaf.obj.map f).hom (((globalSectionsRingHom X).app U).hom s) =
      ((globalSectionsRingHom X).app V).hom s := sorry

section

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{u, w}] [UnivLE.{u, z}]

/-- A map on module global sections commutes with every limit projection to local sections. -/
@[stacks 0D6H "module global-sections map", reassoc (attr := simp)]
theorem map_π {F G : ModuleCat.{z} X} (f : F ⟶ G) (U : Xᵒᵖ) :
    (moduleGlobalSectionsFunctor.{z} X).map f ≫
        limit.π (moduleGlobalSectionsDiagram X G) U =
      limit.π (moduleGlobalSectionsDiagram X F) U ≫
        ((moduleGlobalSectionsPresheaf.{z} X).map f).app U := sorry

/-- A module global-sections map is computed objectwise by the underlying map of restricted
presheaves. -/
@[simp]
theorem map_π_apply
    {F G : ModuleCat.{z} X} (f : F ⟶ G)
    (s : moduleGlobalSectionsObject X F) (U : Xᵒᵖ) :
    (limit.π (moduleGlobalSectionsDiagram X G) U).hom
        (((moduleGlobalSectionsFunctor.{z} X).map f).hom s) =
      (((moduleGlobalSectionsPresheaf.{z} X).map f).app U).hom
        ((limit.π (moduleGlobalSectionsDiagram X F) U).hom s) := sorry

end

end ModuleSections

end RingedSite.Hom
