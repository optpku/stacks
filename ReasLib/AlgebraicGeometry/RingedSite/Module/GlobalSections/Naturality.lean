/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.CategoryTheory.Sites.GlobalSections.Naturality

/-!
# Naturality of module global sections on ringed sites

This module specializes the direct-image naturality of sheaf global sections to module sheaves on
arbitrary ringed sites.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

namespace ModuleSections

/-- The underived global-sections comparison from module sheaves on `X` to global sections after
direct image along a morphism `X ⟶ Y` of ringed sites. -/
@[stacks 0D6H "global-sections pushforward naturality"]
noncomputable def pushforwardNat
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{uX, z}] [UnivLE.{uY, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasWeakSheafify Y.siteTopology AddCommGrpCat.{z}] :
    moduleGlobalSectionsAdditiveFunctor.{z} X ⟶
      f.modulePushforward.{z} ⋙ moduleGlobalSectionsAdditiveFunctor.{z} Y :=
  Functor.whiskerLeft
    (SheafOfModules.toSheaf.{z} X.structureSheaf)
    (@Sheaf.globalSectionsPushforwardNat _ _ _ _ _ _
      f.base Y.siteTopology X.siteTopology f.base_isContinuous _ _ _ _ _ _)

/-- The direct-image global-sections comparison on a module sheaf is the underlying sheaf
global-sections comparison evaluated after forgetting its module structure. -/
@[simp]
theorem pushforwardNat_app
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{uX, z}] [UnivLE.{uY, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasWeakSheafify Y.siteTopology AddCommGrpCat.{z}]
    (ℱ : ModuleCat.{z} X) :
    (pushforwardNat.{z} f).app ℱ =
      (@Sheaf.globalSectionsPushforwardNat _ _ _ _ _ _
        f.base Y.siteTopology X.siteTopology f.base_isContinuous _ _ _ _ _ _).app
        ((SheafOfModules.toSheaf.{z} X.structureSheaf).obj ℱ) := sorry

end ModuleSections

section ModuleValued

namespace ModuleSections

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}]
variable [UnivLE.{uX, z}] [UnivLE.{uY, z}]

/-- Restriction of compatible sections preserves addition and global scalars, and commutes
with the transition maps of the direct-image section diagram. -/
private theorem moduleGlobalSectionsPushforwardNatApp_laws
    (F : RingedSite.ModuleCat.{z} X) :
    let source := (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).obj
      ((moduleGlobalSectionsFunctor.{z} X).obj F)
    let target := moduleGlobalSectionsDiagram Y (f.modulePushforward.{z}.obj F)
    let restrict : ∀ V : Yᵒᵖ, source → target.obj V := fun V s ↦
      (limit.π (moduleGlobalSectionsDiagram X F) (op (f.base.obj V.unop))).hom s
    (∀ V (s t : source), restrict V (s + t) = restrict V s + restrict V t) ∧
    (∀ V (r : globalSectionsRing Y) (s : source),
      restrict V (r • s) = r • restrict V s) ∧
    (∀ {V W : Yᵒᵖ} (g : V ⟶ W) (s : source),
      restrict W s = (target.map g).hom (restrict V s)) := sorry

/-- The component of module-valued global-sections naturality.  It is the compatible section
whose value at `V` is the section over `f.base.obj V` of the source module. -/
noncomputable def moduleGlobalSectionsPushforwardNatApp
    (F : RingedSite.ModuleCat.{z} X) :
    (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
      _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
        _root_.ModuleCat.{z} (globalSectionsRing Y)).obj
        ((moduleGlobalSectionsFunctor.{z} X).obj F) ⟶
      (moduleGlobalSectionsFunctor.{z} Y).obj (f.modulePushforward.{z}.obj F) :=
  let c : Cone (moduleGlobalSectionsDiagram Y (f.modulePushforward.{z}.obj F)) :=
    { pt := (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
        _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
          _root_.ModuleCat.{z} (globalSectionsRing Y)).obj
        ((moduleGlobalSectionsFunctor.{z} X).obj F)
      π :=
        { app := fun V =>
            let source := (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
              _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
                _root_.ModuleCat.{z} (globalSectionsRing Y)).obj
              ((moduleGlobalSectionsFunctor.{z} X).obj F)
            let target := (moduleGlobalSectionsDiagram Y
              (f.modulePushforward.{z}.obj F)).obj V
            @ModuleCat.ofHom (globalSectionsRing Y) _ (source : Type _)
              (target : Type _)
              (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
              (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
              { toFun := fun s =>
                  (limit.π (moduleGlobalSectionsDiagram X F)
                    (op (f.base.obj V.unop))).hom s
                map_add' := (moduleGlobalSectionsPushforwardNatApp_laws f F).1 V
                map_smul' := (moduleGlobalSectionsPushforwardNatApp_laws f F).2.1 V }
          naturality := by
            intro V W g
            ext s
            exact (moduleGlobalSectionsPushforwardNatApp_laws f F).2.2 g s } }
  limit.lift (moduleGlobalSectionsDiagram Y (f.modulePushforward.{z}.obj F)) c

/-- Restriction of compatible module sections commutes with morphisms of module sheaves. -/
private theorem moduleGlobalSectionsPushforwardNat_naturality
    {F G : RingedSite.ModuleCat.{z} X} (α : F ⟶ G) :
    (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).map
        ((moduleGlobalSectionsFunctor.{z} X).map α) ≫
        moduleGlobalSectionsPushforwardNatApp f G =
      moduleGlobalSectionsPushforwardNatApp f F ≫
        (moduleGlobalSectionsFunctor.{z} Y).map (f.modulePushforward.{z}.map α) := sorry

/-- Module-valued global sections commute with direct image after restriction of scalars along the
global-sections ring map. -/
@[stacks 0D6H "module global-sections naturality"]
noncomputable def moduleGlobalSectionsPushforwardNat :
    moduleGlobalSectionsFunctor.{z} X ⋙
        (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
          _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
            _root_.ModuleCat.{z} (globalSectionsRing Y)) ⟶
      f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y where
  app := moduleGlobalSectionsPushforwardNatApp f
  naturality := fun _ _ α ↦ moduleGlobalSectionsPushforwardNat_naturality f α

/-- Sectionwise identity functions respect the global scalar actions in both directions
and identify the transition maps of the restricted and direct-image diagrams. -/
private theorem moduleGlobalSectionsPushforwardDiagramIso_laws
    (F : RingedSite.ModuleCat.{z} X) :
    let source := f.base.op ⋙ (moduleGlobalSectionsDiagram.{z} X F ⋙
      globalSectionsRestriction.{z, uX, vX, uY, vY, w} f)
    let target := moduleGlobalSectionsDiagram.{z} Y (f.modulePushforward.{z}.obj F)
    let forward : ∀ V : Yᵒᵖ, source.obj V → target.obj V := fun V s ↦ s
    let backward : ∀ V : Yᵒᵖ, target.obj V → source.obj V := fun V s ↦ s
    (∀ V (r : globalSectionsRing Y) (s : source.obj V),
      forward V (r • s) = r • forward V s) ∧
    (∀ V (r : globalSectionsRing Y) (s : target.obj V),
      backward V (r • s) = r • backward V s) ∧
    (∀ {V W : Yᵒᵖ} (g : V ⟶ W) (s : source.obj V),
      forward W ((source.map g).hom s) = (target.map g).hom (forward V s)) := sorry

/-- The diagram after restricting global scalars is the actual section diagram of the
module direct image. Both component maps retain the section value. -/
noncomputable def moduleGlobalSectionsPushforwardDiagramIso (F : RingedSite.ModuleCat.{z} X) :
    f.base.op ⋙ (moduleGlobalSectionsDiagram.{z} X F ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) ≅
      moduleGlobalSectionsDiagram.{z} Y (f.modulePushforward.{z}.obj F) :=
  NatIso.ofComponents (fun V ↦ by
    let source := (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).obj
      ((moduleGlobalSectionsDiagram.{z} X F).obj (f.base.op.obj V))
    let target := (moduleGlobalSectionsDiagram.{z} Y (f.modulePushforward.{z}.obj F)).obj V
    exact {
      hom := @_root_.ModuleCat.ofHom (globalSectionsRing Y) _ (source : Type z) (target : Type z)
        source.isAddCommGroup source.isModule target.isAddCommGroup target.isModule
        { toFun := fun s ↦ s
          map_add' := by intros; rfl
          map_smul' := (moduleGlobalSectionsPushforwardDiagramIso_laws f F).1 V }
      inv := @_root_.ModuleCat.ofHom (globalSectionsRing Y) _ (target : Type z) (source : Type z)
        target.isAddCommGroup target.isModule source.isAddCommGroup source.isModule
        { toFun := fun s ↦ s
          map_add' := by intros; rfl
          map_smul' := (moduleGlobalSectionsPushforwardDiagramIso_laws f F).2.1 V }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by
        intro V W g
        ext s
        exact (moduleGlobalSectionsPushforwardDiagramIso_laws f F).2.2 g s)

/-- Restriction of scalars, native initial reindexing, and the sectionwise identity comparison
supply both directions of the global-sections comparison. -/
noncomputable def moduleGlobalSectionsPushforwardLimitIso (F : RingedSite.ModuleCat.{z} X) :
    (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).obj ((moduleGlobalSectionsFunctor.{z} X).obj F) ≅
      (moduleGlobalSectionsFunctor.{z} Y).obj (f.modulePushforward.{z}.obj F) := by
  exact preservesLimitIso (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) (moduleGlobalSectionsDiagram.{z} X F) ≪≫
    (@Functor.Initial.limitIso _ _ _ _ f.base.op
      (@Functor.initial_op_of_final _ _ _ _ f.base
        (@CategoryTheory.final_of_representablyFlat _ _ _ _ f.base
          f.base_representablyFlat)) _ _
      (moduleGlobalSectionsDiagram.{z} X F ⋙
        globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) _).symm ≪≫
    HasLimit.isoOfNatIso (moduleGlobalSectionsPushforwardDiagramIso f F)

/-- Restriction of sections and the native limit inverse are mutually inverse, and the
forward maps commute with morphisms of module sheaves. -/
private theorem moduleGlobalSectionsPushforwardNatIso_laws :
    (∀ F : RingedSite.ModuleCat.{z} X,
      moduleGlobalSectionsPushforwardNatApp f F ≫
        (moduleGlobalSectionsPushforwardLimitIso f F).inv = 𝟙 _) ∧
    (∀ F : RingedSite.ModuleCat.{z} X,
      (moduleGlobalSectionsPushforwardLimitIso f F).inv ≫
        moduleGlobalSectionsPushforwardNatApp f F = 𝟙 _) ∧
    (∀ {F G : RingedSite.ModuleCat.{z} X} (α : F ⟶ G),
      (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).map
          ((moduleGlobalSectionsFunctor.{z} X).map α) ≫
          moduleGlobalSectionsPushforwardNatApp f G =
        moduleGlobalSectionsPushforwardNatApp f F ≫
          (moduleGlobalSectionsFunctor.{z} Y).map (f.modulePushforward.{z}.map α)) := sorry

/-- The canonical comparison keeps the original restriction formula and uses the native
limit inverse as its reverse map. -/
@[stacks 0D6H "module global-sections pushforward isomorphism"]
noncomputable def moduleGlobalSectionsPushforwardNatIso :
    moduleGlobalSectionsFunctor.{z} X ⋙
        (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
          _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
            _root_.ModuleCat.{z} (globalSectionsRing Y)) ≅
      f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y :=
  NatIso.ofComponents (fun F ↦
    { hom := moduleGlobalSectionsPushforwardNatApp f F
      inv := (moduleGlobalSectionsPushforwardLimitIso f F).inv
      hom_inv_id := (moduleGlobalSectionsPushforwardNatIso_laws f).1 F
      inv_hom_id := (moduleGlobalSectionsPushforwardNatIso_laws f).2.1 F })
    (fun {_ _} α ↦ (moduleGlobalSectionsPushforwardNatIso_laws f).2.2 α)

/-- The original module-valued comparison is invertible using the displayed limit inverse. -/
@[stacks 0D6H "module global-sections pushforward isomorphism"]
theorem moduleGlobalSectionsPushforwardNat_isIso :
    IsIso (moduleGlobalSectionsPushforwardNat f) := by
  change IsIso (moduleGlobalSectionsPushforwardNatIso f).hom
  infer_instance

/-- The reverse comparison is the inverse of the native limit comparison. -/
@[simp]
theorem moduleGlobalSectionsPushforwardNatIso_inv_app (F : RingedSite.ModuleCat.{z} X) :
    (moduleGlobalSectionsPushforwardNatIso f).inv.app F =
      (moduleGlobalSectionsPushforwardLimitIso f F).inv := rfl

end ModuleSections

end ModuleValued

end RingedSite.Hom
