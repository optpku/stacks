/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule

/-!
# Pullback-sections module presheaves

This module re-exports the reusable construction of the module presheaf whose values are
global sections of pullbacks.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v w

variable {C : Type w} [Category.{v} C] {B : Scheme.{u}}
variable (p : C ⥤ CategoryTheory.Over B) (F : B.Modules)

#check (AlgebraicGeometry.Scheme.Over.structurePresheaf p : Cᵒᵖ ⥤ RingCat.{u})

#check (AlgebraicGeometry.Scheme.Site.structurePresheaf_obj
  (p ⋙ CategoryTheory.Over.forget B) :
    ∀ U : C, (AlgebraicGeometry.Scheme.Over.structurePresheaf p).obj (op U) =
      RingCat.of Γ((p.obj U).left, ⊤))

#check (AlgebraicGeometry.Scheme.Site.structurePresheaf_map
  (p ⋙ CategoryTheory.Over.forget B) :
    ∀ {U V : C} (f : U ⟶ V),
      (AlgebraicGeometry.Scheme.Over.structurePresheaf p).map f.op =
        RingCat.ofHom ((p.map f).left.appTop).hom)

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F :
  ∀ U : Cᵒᵖ,
    ModuleCat.{u} ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).obj U))

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_smul p F :
  ∀ {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (AlgebraicGeometry.Scheme.Over.structurePresheaf p).obj U)
    (s : AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F U),
    (AlgebraicGeometry.Scheme.Modules.PullbackSections.map F (p.map f.unop)).hom (r • s) =
      @SMul.smul ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).obj V)
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F V)
        (ModuleCat.isModule
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F V)).toSMul
        ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map f r)
        ((AlgebraicGeometry.Scheme.Modules.PullbackSections.map F
          (p.map f.unop)).hom s))

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F :
  ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F U ⟶
      (ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map f).hom).obj
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F V))

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_id p F :
  ∀ U : Cᵒᵖ,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom
          ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map_id U))).inv.app _)

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_comp p F :
  ∀ {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F (f ≫ g) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F f ≫
        (ModuleCat.restrictScalars
          ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map f).hom).map
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F g) ≫
        (ModuleCat.restrictScalarsComp'
          ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map f).hom
          ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map g).hom
          ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom
            ((AlgebraicGeometry.Scheme.Over.structurePresheaf p).map_comp f g))).inv.app _)

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf p F :
  PresheafOfModules (AlgebraicGeometry.Scheme.Over.structurePresheaf p))

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf_obj p F :
  ∀ U : Cᵒᵖ,
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf p F).obj U =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj p F U)

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf_map p F :
  ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf p F).map f =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap p F f)
