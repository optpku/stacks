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

/-- Evaluation of compatible global sections is the corresponding limit projection. -/
theorem moduleSectionsEquiv_apply
    (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{uX, w}] (M : SheafOfModules.{w} X.structureSheaf)
    (s : Hom.moduleGlobalSectionsObject.{w} X M) (U : X.carrierᵒᵖ) :
    (moduleSectionsEquiv X M s).val U =
      (limit.π (Hom.moduleGlobalSectionsDiagram X M) U) s := by
  change limit.π (Hom.moduleGlobalSectionsDiagram X M ⋙
      forget (_root_.ModuleCat.{w} (Hom.globalSectionsRing X))) U
      ((preservesLimitIso (forget (_root_.ModuleCat.{w} (Hom.globalSectionsRing X)))
        (Hom.moduleGlobalSectionsDiagram X M)).hom s) = _
  exact CategoryTheory.congr_fun (preservesLimitIso_hom_π
    (forget (_root_.ModuleCat.{w} (Hom.globalSectionsRing X)))
    (Hom.moduleGlobalSectionsDiagram X M) U) s

/-- The limit-to-sections comparison commutes with module-sheaf morphisms. -/
theorem moduleSectionsEquiv_naturality
    (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{uX, w}] {M N : SheafOfModules.{w} X.structureSheaf}
    (g : M ⟶ N) (s : Hom.moduleGlobalSectionsObject.{w} X M) :
    moduleSectionsEquiv X N ((Hom.moduleGlobalSectionsFunctor.{w} X).map g s) =
      (Functor.sectionsFunctor _).map
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).map g).hom
        (moduleSectionsEquiv X M s) := by
  -- Use the same site-sized limits as the global-sections functor.
  letI := Hom.moduleGlobalSectionsHasLimitsOfShape.{w} X
  apply Subtype.ext
  funext U
  rw [moduleSectionsEquiv_apply]
  change (limit.π (Hom.moduleGlobalSectionsDiagram X N) U)
      (lim.map (Hom.moduleGlobalSectionsDiagramMap X g) s) =
    g.val.app U ((moduleSectionsEquiv X M s).val U)
  rw [moduleSectionsEquiv_apply]
  exact CategoryTheory.congr_fun (limMap_π (Hom.moduleGlobalSectionsDiagramMap X g) U) s

private theorem terminalSections_naturality
    {C : Type uX} [Category.{vX} C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type w)} (g : F ⟶ G) (s : F.obj.sections) :
    Sheaf.sectionsTerminalHomEquiv G ((Functor.sectionsFunctor _).map g.hom s) =
      Sheaf.sectionsTerminalHomEquiv F s ≫ g := by
  ext U x
  rfl

private theorem pushforwardSections_naturality
    {C : Type uX} [Category.{vX} C] {J : GrothendieckTopology C}
    {D : Type uY} [Category.{vY} D] {K : GrothendieckTopology D}
    (f : MorphismOfTopoiIn.{uX, uY, vX, vY, w} J K)
    {F G : Sheaf K (Type w)} (g : F ⟶ G)
    (s : (f.pushforward.obj F).obj.sections) :
    f.pushforwardSectionsEquiv G
        ((Functor.sectionsFunctor _).map (f.pushforward.map g).hom s) =
      (Functor.sectionsFunctor _).map g.hom (f.pushforwardSectionsEquiv F s) := by
  apply (Sheaf.sectionsTerminalHomEquiv G).injective
  change Sheaf.sectionsTerminalHomEquiv G
      ((Sheaf.sectionsTerminalHomEquiv G).symm _) = _
  rw [Equiv.apply_symm_apply, terminalSections_naturality,
    terminalSections_naturality,
    f.adjunction.homEquiv_naturality_right_symm]
  change _ = Sheaf.sectionsTerminalHomEquiv F
    ((Sheaf.sectionsTerminalHomEquiv F).symm _) ≫ g
  rw [Equiv.apply_symm_apply, Category.assoc]

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

/-- The compatible-section comparison for module direct image is natural. -/
theorem modulePushforwardSectionsEquiv_naturality
    {M N : SheafOfModules.{w} X.structureSheaf} (g : M ⟶ N)
    (s : ((Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj
      (f.modulePushforward.obj M)).obj.sections) :
    f.modulePushforwardSectionsEquiv N
        ((Functor.sectionsFunctor _).map
          ((Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).map
            (f.modulePushforward.map g)).hom s) =
      (Functor.sectionsFunctor _).map
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).map g).hom
        (f.modulePushforwardSectionsEquiv M s) := by
  change f.toTopos.pushforwardSectionsEquiv _
      ((Functor.sectionsFunctor _).map ((ModulePushforward.forgetIso f).hom.app N).hom
        ((Functor.sectionsFunctor _).map
          ((Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).map
            (f.modulePushforward.map g)).hom s)) =
    (Functor.sectionsFunctor _).map
      ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).map g).hom
      (f.toTopos.pushforwardSectionsEquiv _
        ((Functor.sectionsFunctor _).map ((ModulePushforward.forgetIso f).hom.app M).hom s))
  rw [← pushforwardSections_naturality f.toTopos
    ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).map g)]
  apply congrArg (f.toTopos.pushforwardSectionsEquiv _)
  apply Subtype.ext
  funext U
  have h := congrArg ((sheafToPresheaf Y.siteTopology (Type w)).map)
    ((ModulePushforward.forgetIso f).hom.naturality g)
  simp only [Functor.map_comp] at h
  have hU := NatTrans.congr_app h U
  simp only [NatTrans.comp_app] at hU
  exact types_congr_hom hU (s.val U)

/-- The global-sections comparison as an equivalence of underlying elements. -/
noncomputable def moduleGlobalSectionsPushforwardEquiv
    (M : SheafOfModules.{w} X.structureSheaf) :
    Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M) ≃
      Hom.moduleGlobalSectionsObject.{w} X M :=
  (moduleSectionsEquiv Y (f.modulePushforward.obj M)).trans
    ((f.modulePushforwardSectionsEquiv M).trans (moduleSectionsEquiv X M).symm)

/-- The global-section comparison commutes with module-sheaf morphisms. -/
theorem moduleGlobalSectionsPushforwardEquiv_naturality
    {M N : SheafOfModules.{w} X.structureSheaf} (g : M ⟶ N)
    (s : Hom.moduleGlobalSectionsObject.{w} Y (f.modulePushforward.obj M)) :
    f.moduleGlobalSectionsPushforwardEquiv N
        ((Hom.moduleGlobalSectionsFunctor.{w} Y).map (f.modulePushforward.map g) s) =
      (Hom.moduleGlobalSectionsFunctor.{w} X).map g
        (f.moduleGlobalSectionsPushforwardEquiv M s) := by
  apply (moduleSectionsEquiv X N).injective
  rw [moduleSectionsEquiv_naturality]
  simp only [moduleGlobalSectionsPushforwardEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply, moduleSectionsEquiv_naturality,
    modulePushforwardSectionsEquiv_naturality]

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
      map_add' := by
        intro x y
        apply (f.moduleGlobalSectionsPushforwardEquiv M).injective
        change (f.moduleGlobalSectionsPushforwardHom M) _ =
          (f.moduleGlobalSectionsPushforwardHom M) (_ + _)
        rw [map_add]
        change (f.moduleGlobalSectionsPushforwardEquiv M)
            ((f.moduleGlobalSectionsPushforwardEquiv M).symm (x + y)) =
          (f.moduleGlobalSectionsPushforwardEquiv M)
              ((f.moduleGlobalSectionsPushforwardEquiv M).symm x) +
            (f.moduleGlobalSectionsPushforwardEquiv M)
              ((f.moduleGlobalSectionsPushforwardEquiv M).symm y)
        simp only [Equiv.apply_symm_apply]
        rfl
      map_smul' := by
        intro r x
        apply (f.moduleGlobalSectionsPushforwardEquiv M).injective
        change (f.moduleGlobalSectionsPushforwardHom M) _ =
          (f.moduleGlobalSectionsPushforwardHom M) (r • _)
        rw [map_smul]
        change (f.moduleGlobalSectionsPushforwardEquiv M)
            ((f.moduleGlobalSectionsPushforwardEquiv M).symm (r • x)) =
          r • (show source from (f.moduleGlobalSectionsPushforwardEquiv M)
            ((f.moduleGlobalSectionsPushforwardEquiv M).symm x))
        simp only [Equiv.apply_symm_apply] }

/-- The module-valued global-section/direct-image natural isomorphism, with
both maps constructed from the topos adjunction rather than chosen. -/
noncomputable def moduleGlobalSectionsPushforwardIso :
    f.modulePushforward ⋙ Hom.moduleGlobalSectionsFunctor.{w} Y ≅
      Hom.moduleGlobalSectionsFunctor.{w} X ⋙ f.globalSectionsRestriction :=
  NatIso.ofComponents
    (fun M ↦
      { hom := f.moduleGlobalSectionsPushforwardHom M
        inv := f.moduleGlobalSectionsPushforwardInv M
        hom_inv_id := by
          ext x
          exact (f.moduleGlobalSectionsPushforwardEquiv M).symm_apply_apply x
        inv_hom_id := by
          ext x
          exact (f.moduleGlobalSectionsPushforwardEquiv M).apply_symm_apply x })
    (by
      intro M N g
      ext s
      exact f.moduleGlobalSectionsPushforwardEquiv_naturality g s)

end RingedSite.ToposHom
