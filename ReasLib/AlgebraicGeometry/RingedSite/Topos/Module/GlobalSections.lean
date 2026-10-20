/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w

namespace RingedSite.ToposHom

/-- The module of global sections has the same elements as the compatible
sections of the underlying type-valued sheaf. -/
noncomputable def moduleSectionsEquiv
    (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{uX, w}] (M : SheafOfModules.{w} X.structureSheaf) :
    Hom.moduleGlobalSectionsObject.{w} X M ≃
      ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M).obj.sections :=
  (preservesLimitIso (forget (_root_.ModuleCat.{w} (Hom.globalSectionsRing X)))
    (Hom.moduleGlobalSectionsDiagram X M)).toEquiv.trans
      (Types.limitEquivSections _)

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable (f : ToposHom X Y)

/-- Scalar restriction along the actual global-sections ring map. -/
noncomputable abbrev globalSectionsRestriction :=
  _root_.ModuleCat.restrictScalars.{w} f.globalSectionsMap.hom

/-- Compatible sections of a module direct image are canonically the
compatible sections of the source module. -/
noncomputable def modulePushforwardSectionsEquiv (M : SheafOfModules.{w} X.structureSheaf) :
    ((Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj
      (f.modulePushforward.obj M)).obj.sections ≃
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M).obj.sections :=
  ((Functor.sectionsFunctor _).mapIso
    ((sheafToPresheaf Y.siteTopology (Type w)).mapIso
      ((ModulePushforward.forgetIso f).app M))).toEquiv.trans
    (f.toTopos.pushforwardSectionsEquiv
      ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M))

/-- The global-sections comparison as an equivalence of underlying elements. -/
noncomputable def moduleGlobalSectionsPushforwardEquiv
    (M : SheafOfModules.{w} X.structureSheaf) :
    Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M) ≃
      Hom.moduleGlobalSectionsObject.{w} X M :=
  (moduleSectionsEquiv Y (f.modulePushforward.obj M)).trans
    ((f.modulePushforwardSectionsEquiv M).trans (moduleSectionsEquiv X M).symm)

/-- Global sections of a direct image map linearly to the scalar-restricted
global sections on the source, with the canonical section function. -/
noncomputable def moduleGlobalSectionsPushforwardHom
    (M : SheafOfModules.{w} X.structureSheaf) :
    Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M) ⟶
      f.globalSectionsRestriction.obj (Hom.moduleGlobalSectionsObject.{w} X M) :=
  let source := Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M)
  let target := f.globalSectionsRestriction.obj (Hom.moduleGlobalSectionsObject.{w} X M)
  @_root_.ModuleCat.ofHom (Hom.globalSectionsRing Y) _ source target
    source.isAddCommGroup source.isModule target.isAddCommGroup target.isModule
    { toFun := f.moduleGlobalSectionsPushforwardEquiv M
      map_add' := sorry
      map_smul' := sorry }

/-- The reverse module map is the inverse canonical section function. -/
noncomputable def moduleGlobalSectionsPushforwardInv
    (M : SheafOfModules.{w} X.structureSheaf) :
    f.globalSectionsRestriction.obj (Hom.moduleGlobalSectionsObject.{w} X M) ⟶
      Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M) :=
  let source := f.globalSectionsRestriction.obj (Hom.moduleGlobalSectionsObject.{w} X M)
  let target := Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M)
  @_root_.ModuleCat.ofHom (Hom.globalSectionsRing Y) _ source target
    source.isAddCommGroup source.isModule target.isAddCommGroup target.isModule
    { toFun := (f.moduleGlobalSectionsPushforwardEquiv M).symm
      map_add' := sorry
      map_smul' := sorry }

/-- The module-valued global-section/direct-image natural isomorphism, with
both maps constructed from the topos adjunction rather than chosen. -/
noncomputable def moduleGlobalSectionsPushforwardIso :
    f.modulePushforward ⋙ Hom.moduleGlobalSectionsFunctor.{w} Y ≅
      Hom.moduleGlobalSectionsFunctor.{w} X ⋙ f.globalSectionsRestriction :=
  NatIso.ofComponents
    (fun M ↦
      { hom := f.moduleGlobalSectionsPushforwardHom M
        inv := f.moduleGlobalSectionsPushforwardInv M
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end RingedSite.ToposHom
