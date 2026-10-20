module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Components of modules on a simplicial scheme

Restriction to a stage and the pullback comparisons along simplex operators.
-/

-- Exposed constructions use private implementation bodies without exporting their names.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite AlgebraicGeometry
open TopCat TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

namespace QCoh

/-- Package a quasi-coherent module sheaf as an object of the quasi-coherent category. -/
def of {U : SimplicialObject Scheme.{u}}
    (F : SheafOfModules.{u} (structureSheaf U)) [F.IsQuasicoherent] : QCoh U :=
  ⟨F, inferInstance⟩

/-- The underlying module sheaf of the quasi-coherent constructor is the given sheaf. -/
theorem of_obj {U : SimplicialObject Scheme.{u}}
    (F : SheafOfModules.{u} (structureSheaf U)) [F.IsQuasicoherent] :
    (of F).obj = F := rfl

/-- Inclusion of quasi-coherent modules returns the underlying module sheaf. -/
theorem inclusion_obj (U : SimplicialObject Scheme.{u}) (F : QCoh U) :
    (inclusion U).obj F = F.obj := rfl

end QCoh

private def moduleComponentHom {U : SimplicialObject Scheme.{u}} {n : SimplexCategoryᵒᵖ}
    {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (f : W ⟶ Z) :
    DiagramOpens.ofOpens (forgetToTop.obj U) n Z.unop ⟶
      DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop :=
  DiagramOpens.homOfLE (leOfHom f.unop)

private theorem moduleComponentHom_structureMap {U : SimplicialObject Scheme.{u}}
    {n : SimplexCategoryᵒᵖ} {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (f : W ⟶ Z) :
    ((structureSheaf U).obj.map (moduleComponentHom f).op).hom =
      ((U.obj n).ringCatSheaf.obj.map f).hom := sorry

private def moduleComponentPresheafMap (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : SheafOfModules.{u} (structureSheaf U))
    {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (f : W ⟶ Z) :=
  F.val.map (moduleComponentHom f).op ≫
    (ModuleCat.restrictScalarsCongr (moduleComponentHom_structureMap f)).hom.app _

private theorem moduleComponentPresheaf_laws (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : SheafOfModules.{u} (structureSheaf U)) :
    (∀ W, moduleComponentPresheafMap U n F (𝟙 W) =
      (ModuleCat.restrictScalarsId' ((U.obj n).ringCatSheaf.obj.map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom ((U.obj n).ringCatSheaf.obj.map_id W))).inv.app _) ∧
    (∀ {W Z T} (f : W ⟶ Z) (g : Z ⟶ T),
      moduleComponentPresheafMap U n F (f ≫ g) =
        moduleComponentPresheafMap U n F f ≫
          (ModuleCat.restrictScalars _).map (moduleComponentPresheafMap U n F g) ≫
            (ModuleCat.restrictScalarsComp' ((U.obj n).ringCatSheaf.obj.map f).hom
              ((U.obj n).ringCatSheaf.obj.map g).hom
              ((U.obj n).ringCatSheaf.obj.map (f ≫ g)).hom
              (congrArg RingCat.Hom.hom ((U.obj n).ringCatSheaf.obj.map_comp f g))).inv.app _) :=
  sorry

private def moduleComponentPresheaf (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : SheafOfModules.{u} (structureSheaf U)) :
    PresheafOfModules.{u} (U.obj n).ringCatSheaf.obj where
  obj W := F.val.obj (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop))
  map f := moduleComponentPresheafMap U n F f
  map_id := (moduleComponentPresheaf_laws U n F).1
  map_comp := (moduleComponentPresheaf_laws U n F).2

private theorem moduleComponent_isSheaf (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : SheafOfModules.{u} (structureSheaf U)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (U.obj n))
      (moduleComponentPresheaf U n F).presheaf := sorry

private theorem moduleComponent_map_naturality (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) {F H : SheafOfModules.{u} (structureSheaf U)} (f : F ⟶ H)
    {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (g : W ⟶ Z) :
    (moduleComponentPresheaf U n F).map g ≫
        (ModuleCat.restrictScalars ((U.obj n).ringCatSheaf.obj.map g).hom).map
          (f.val.app (op (DiagramOpens.ofOpens (forgetToTop.obj U) n Z.unop))) =
      f.val.app (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop)) ≫
        (moduleComponentPresheaf U n H).map g := sorry

private def moduleComponentMap (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)
    {F H : SheafOfModules.{u} (structureSheaf U)} (f : F ⟶ H) :
    (⟨moduleComponentPresheaf U n F, moduleComponent_isSheaf U n F⟩ : (U.obj n).Modules) ⟶
      ⟨moduleComponentPresheaf U n H, moduleComponent_isSheaf U n H⟩ :=
  ⟨{ app := fun W ↦ f.val.app (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop))
     naturality := moduleComponent_map_naturality U n f }⟩

private theorem moduleComponent_laws (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) :
    (∀ F, moduleComponentMap U n (𝟙 F) = 𝟙 _) ∧
    (∀ {F H K} (f : F ⟶ H) (g : H ⟶ K),
      moduleComponentMap U n (f ≫ g) = moduleComponentMap U n f ≫ moduleComponentMap U n g) :=
  sorry

/-- Restriction of a module sheaf on a simplicial scheme to one stage. -/
def moduleComponent (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.{u} (structureSheaf U) ⥤ (U.obj n).Modules where
  obj F := ⟨moduleComponentPresheaf U n F, moduleComponent_isSheaf U n F⟩
  map f := moduleComponentMap U n f
  map_id := (moduleComponent_laws U n).1
  map_comp := (moduleComponent_laws U n).2

/-- Stage restriction evaluates a sheaf on the corresponding diagram open. -/
theorem moduleComponent_obj (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)
    (F : SheafOfModules.{u} (structureSheaf U))
    (W : Opens ((forgetToTop.obj U).obj n)) :
    ((moduleComponent U n).obj F).val.obj (op W) =
      F.val.obj (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W)) := rfl

/-- Restriction of a quasi-coherent module to any stage is quasi-coherent. -/
instance moduleComponent_isQuasicoherent (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : SheafOfModules.{u} (structureSheaf U))
    [F.IsQuasicoherent] : ((moduleComponent U n).obj F).IsQuasicoherent := sorry

private def simplexDiagramHom (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (V : Opens ((forgetToTop.obj U).obj (op n))) :
    DiagramOpens.ofOpens (forgetToTop.obj U) (op m)
        ((Opens.map ((forgetToTop.obj U).map φ.op)).obj V) ⟶
      DiagramOpens.ofOpens (forgetToTop.obj U) (op n) V :=
  DiagramOpens.homMk φ.op (fun _ hx ↦ hx)

private theorem simplexDiagramHom_base (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (V : Opens ((forgetToTop.obj U).obj (op n))) :
    (simplexDiagramHom U φ V).base = φ.op := rfl

private def stageDirectSection (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U)
    (V : (Opens ((forgetToTop.obj U).obj (op n)))ᵒᵖ) :
    ((moduleComponent U (op n)).obj F.obj).val.obj V →
      ((Scheme.Modules.pushforward (U.map φ.op)).obj
        ((moduleComponent U (op m)).obj F.obj)).val.obj V :=
  fun x ↦ F.obj.val.map (simplexDiagramHom U φ V.unop).op x

private theorem stageDirect_linear (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U)
    (V : (Opens ((forgetToTop.obj U).obj (op n)))ᵒᵖ) :
    (∀ x y, stageDirectSection U φ F V (x + y) =
      stageDirectSection U φ F V x + stageDirectSection U φ F V y) ∧
    (∀ (r : (U.obj (op n)).ringCatSheaf.obj.obj V) x,
      stageDirectSection U φ F V (r • x) = r • stageDirectSection U φ F V x) := sorry

private def stageDirectApp (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U)
    (V : (Opens ((forgetToTop.obj U).obj (op n)))ᵒᵖ) :=
  ModuleCat.ofHom
    { toFun := stageDirectSection U φ F V
      map_add' := (stageDirect_linear U φ F V).1
      map_smul' := (stageDirect_linear U φ F V).2 }

private theorem stageDirect_naturality (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U)
    {V W : (Opens ((forgetToTop.obj U).obj (op n)))ᵒᵖ} (g : V ⟶ W) :
    ((moduleComponent U (op n)).obj F.obj).val.map g ≫
        (ModuleCat.restrictScalars ((U.obj (op n)).ringCatSheaf.obj.map g).hom).map
          (stageDirectApp U φ F W) =
      stageDirectApp U φ F V ≫
        ((Scheme.Modules.pushforward (U.map φ.op)).obj
          ((moduleComponent U (op m)).obj F.obj)).val.map g := sorry

/-- The direct-image comparison induced by restriction along a simplex operator. -/
def stageDirect (U : SimplicialObject Scheme.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (F : QCoh U) :
    (moduleComponent U (op n)).obj F.obj ⟶
      (Scheme.Modules.pushforward (U.map φ.op)).obj
        ((moduleComponent U (op m)).obj F.obj) where
  val := { app := stageDirectApp U φ F
           naturality := stageDirect_naturality U φ F }

/-- The pullback comparison along a simplex operator, obtained by adjunction. -/
def stageRestrictModules (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U) :
    (Scheme.Modules.pullback (U.map φ.op)).obj
      ((moduleComponent U (op n)).obj F.obj) ⟶
      (moduleComponent U (op m)).obj F.obj :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (U.map φ.op)).homEquiv
      ((moduleComponent U (op n)).obj F.obj)
      ((moduleComponent U (op m)).obj F.obj)).symm (stageDirect U φ F)

/-- Adjunction sends the pullback comparison to the direct-image comparison. -/
theorem stageRestrictModules_homEquiv (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (U.map φ.op)).homEquiv
        ((moduleComponent U (op n)).obj F.obj)
        ((moduleComponent U (op m)).obj F.obj)) (stageRestrictModules U φ F) =
      stageDirect U φ F := Equiv.apply_symm_apply _ _

/-- Simplex-operator comparisons of quasi-coherent modules are isomorphisms. -/
instance stageRestrictModules_isIso (U : SimplicialObject Scheme.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : QCoh U) :
    IsIso (stageRestrictModules U φ F) := sorry

end AlgebraicGeometry.SimplicialObject
