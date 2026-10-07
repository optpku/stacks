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
    (Sheaf.globalSectionsPushforwardNat
      f.base Y.siteTopology X.siteTopology)

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
      (Sheaf.globalSectionsPushforwardNat
        f.base Y.siteTopology X.siteTopology).app
        ((SheafOfModules.toSheaf.{z} X.structureSheaf).obj ℱ) := sorry

end ModuleSections

section ModuleValued

namespace ModuleSections

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}]
variable [UnivLE.{uX, z}] [UnivLE.{uY, z}]

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
                map_add' := sorry
                map_smul' := sorry }
          naturality := sorry } }
  limit.lift (moduleGlobalSectionsDiagram Y (f.modulePushforward.{z}.obj F)) c

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
  naturality := sorry

/-- The module-valued global-sections comparison for a direct image is an isomorphism. -/
@[stacks 0D6H "module global-sections pushforward isomorphism"]
noncomputable instance moduleGlobalSectionsPushforwardNat_isIso :
    IsIso (moduleGlobalSectionsPushforwardNat f) := sorry

/-- The canonical module-valued global-sections isomorphism for a direct image. -/
@[stacks 0D6H "module global-sections pushforward isomorphism"]
noncomputable def moduleGlobalSectionsPushforwardNatIso :
    moduleGlobalSectionsFunctor.{z} X ⋙
        (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
          _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
            _root_.ModuleCat.{z} (globalSectionsRing Y)) ≅
      f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y :=
  asIso (moduleGlobalSectionsPushforwardNat f)

end ModuleSections

end ModuleValued

end RingedSite.Hom
