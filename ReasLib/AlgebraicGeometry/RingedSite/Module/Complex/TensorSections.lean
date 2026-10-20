/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose

/-!
# Tensor complexes and derived sections on a slice site

Coefficients over the section ring at an object give a tensor presheaf on its slice.
Extension to a sheaf of coefficient rings and module sheafification give the associated
complex; tensor insertion and the derived-sections unit give its canonical comparison.
-/

@[expose] public section

open CategoryTheory Opposite ComplexShape
open SheafOfModules.RingedSite

noncomputable section

-- The exposed constructions use private implementation data; this option permits that
-- module boundary without promoting the intermediate functors to public API.
set_option backward.privateInPublic true

universe u v

namespace RingedSite.Hom.TensorSections

variable {C : Type u} [Category.{v} C]

private def constantModules (U : C) (R : CommRingCat.{max u v}) :
    _root_.ModuleCat.{max u v} R ⥤
      PresheafOfModules.{max u v}
        (((Functor.const (Over U)ᵒᵖ).obj R) ⋙ forget₂ CommRingCat RingCat) where
  obj M :=
    { obj := fun _ ↦ M
      map := fun _ ↦ _root_.ModuleCat.ofHom LinearMap.id
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  map f :=
    { app := fun _ ↦ f
      naturality := fun _ ↦ by ext; rfl }
  map_id := fun _ ↦ by ext; rfl
  map_comp := fun _ _ ↦ by ext; rfl

private instance constantModules_additive (U : C) (R : CommRingCat.{max u v}) :
    (constantModules U R).Additive where
  map_add := rfl

private instance tensorExtension_additive {D : Type (max u v)} [Category.{v} D]
    {R T : Dᵒᵖ ⥤ CommRingCat.{max u v}} (α : R ⟶ T) :
    (PresheafOfModules.SameSiteTensorExtension.functor α).Additive :=
  (PresheafOfModules.SameSiteTensorExtension.adjunction α).left_adjoint_additive

variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) (U : C)

/-- Restriction from the section ring at an object to the structure presheaf on its slice. -/
private def sectionMap :
    (Functor.const (Over U)ᵒᵖ).obj (𝒪.obj (op U)) ⟶ (Over.forget U).op ⋙ 𝒪 where
  app V := 𝒪.map V.unop.hom.op
  naturality V W f := by
    change 𝒪.map W.unop.hom.op =
      𝒪.map V.unop.hom.op ≫ 𝒪.map f.unop.left.op
    rw [← 𝒪.map_comp]
    exact congrArg (fun g ↦ 𝒪.map g.op) (Over.w f.unop).symm

private abbrev tensorFunctor :=
  constantModules U (𝒪.obj (op U)) ⋙
    PresheafOfModules.SameSiteTensorExtension.functor (sectionMap 𝒪 U)

/-- The complex of module presheaves on the slice whose value at an arrow to the base
object is extension of scalars of the coefficient complex to the source section ring. -/
def tensorPresheaf (M : CochainComplex (_root_.ModuleCat (𝒪.obj (op U))) ℤ) :
    CochainComplex
      (PresheafOfModules.{max u v} (((Over.forget U).op ⋙ 𝒪) ⋙
        forget₂ CommRingCat RingCat)) ℤ :=
  by exact ((tensorFunctor 𝒪 U).mapHomologicalComplex (up ℤ)).obj M

variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪τ : Sheaf J CommRingCat.{max u v}) (α : 𝒪 ⟶ 𝒪τ.obj)

private abbrev sliceCoefficients :=
  sectionMap 𝒪 U ≫ Functor.whiskerLeft (Over.forget U).op α

private abbrev coefficientMap :=
  ((sliceCoefficients 𝒪 U J 𝒪τ α).app (op (Over.mk (𝟙 U)))).hom

private abbrev sliceRingSheaf := ringSheaf (J.over U) (𝒪τ.over U)

private instance fixedSheafification_additive :
    (moduleSheafification (𝒪τ.over U) :
      PresheafOfModules.{max u v} (sliceRingSheaf U J 𝒪τ).obj ⥤
        SheafOfModules.{max u v} (sliceRingSheaf U J 𝒪τ)).Additive :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (sliceRingSheaf U J 𝒪τ).obj)).left_adjoint_additive

private abbrev associatedFunctor :=
  constantModules U (𝒪.obj (op U)) ⋙
    PresheafOfModules.SameSiteTensorExtension.functor (sliceCoefficients 𝒪 U J 𝒪τ α) ⋙
    moduleSheafification (𝒪τ.over U)

private instance associatedFunctor_additive :
    (associatedFunctor 𝒪 U J 𝒪τ α).Additive where
  map_add := by
    intros
    simp only [associatedFunctor, Functor.comp_map,
      (constantModules_additive U (𝒪.obj (op U))).map_add,
      (tensorExtension_additive (sliceCoefficients 𝒪 U J 𝒪τ α)).map_add]
    exact (fixedSheafification_additive U J 𝒪τ).map_add

/-- The tensor complex associated to a coefficient complex on the slice site, obtained by
extension along the coefficient-sheaf map and degreewise module sheafification. -/
def associatedComplex (M : CochainComplex (_root_.ModuleCat (𝒪.obj (op U))) ℤ) :
    CochainComplex (RingedSite.ModuleCat.{max u v}
      (RingedSite.ofCommRingSheaf J 𝒪τ |>.localization U)) ℤ :=
  by exact ((associatedFunctor 𝒪 U J 𝒪τ α).mapHomologicalComplex (up ℤ)).obj M

private abbrev evaluation :
    RingedSite.ModuleCat.{max u v}
      ((RingedSite.ofCommRingSheaf J 𝒪τ).localization U) ⥤
        _root_.ModuleCat.{max u v} (𝒪τ.obj.obj (op U)) :=
  SheafOfModules.evaluation.{max u v} (sliceRingSheaf U J 𝒪τ) (op (Over.mk (𝟙 U)))

private instance evaluation_additive : (evaluation U J 𝒪τ).Additive :=
  inferInstanceAs ((SheafOfModules.forget (sliceRingSheaf U J 𝒪τ)) ⋙
    PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).Additive

private abbrev scalarRestriction :=
  _root_.ModuleCat.restrictScalars.{max u v} (coefficientMap 𝒪 U J 𝒪τ α)

private def sheafificationUnit :
    𝟭 (PresheafOfModules.{max u v} (sliceRingSheaf U J 𝒪τ).obj) ⟶
      moduleSheafification (𝒪τ.over U) ⋙
        SheafOfModules.forget (sliceRingSheaf U J 𝒪τ) :=
  moduleSheafificationUnit (𝒪τ.over U) ≫
    Functor.whiskerLeft (moduleSheafification (𝒪τ.over U))
      (ValRestriction.natTransInv (𝒪τ.over U))

private def unitTransformation :
    𝟭 (_root_.ModuleCat.{max u v} (𝒪.obj (op U))) ⟶
      associatedFunctor 𝒪 U J 𝒪τ α ⋙ evaluation U J 𝒪τ ⋙
        scalarRestriction 𝒪 U J 𝒪τ α :=
  (_root_.ModuleCat.extendRestrictScalarsAdj (coefficientMap 𝒪 U J 𝒪τ α)).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (constantModules U (𝒪.obj (op U)) ⋙
          PresheafOfModules.SameSiteTensorExtension.functor (sliceCoefficients 𝒪 U J 𝒪τ α))
        (sheafificationUnit U J 𝒪τ))
      (PresheafOfModules.evaluation (sliceRingSheaf U J 𝒪τ).obj
          (op (Over.mk (𝟙 U))) ⋙ scalarRestriction 𝒪 U J 𝒪τ α)

private instance sections_additive :
    (evaluation U J 𝒪τ ⋙ scalarRestriction 𝒪 U J 𝒪τ α).Additive where
  map_add := by
    intros
    simp only [Functor.comp_map, (evaluation_additive U J 𝒪τ).map_add]
    rfl

/-- The chain map to sections of the associated slice complex, induced by tensor insertion
and the unit of module sheafification, with scalars restricted to the original section ring. -/
def unit (M : CochainComplex (_root_.ModuleCat (𝒪.obj (op U))) ℤ) :
    M ⟶ (((evaluation U J 𝒪τ ⋙ scalarRestriction 𝒪 U J 𝒪τ α).mapHomologicalComplex
      (up ℤ)).obj (associatedComplex 𝒪 U J 𝒪τ α M)) where
  f n := (unitTransformation 𝒪 U J 𝒪τ α).app (M.X n)
  comm' i j _ := ((unitTransformation 𝒪 U J 𝒪τ α).naturality (M.d i j)).symm

/-- In each degree the unit is tensor insertion followed by the module-sheafification unit. -/
theorem unit_app (M : CochainComplex (_root_.ModuleCat (𝒪.obj (op U))) ℤ)
    (n : ℤ) :
    (unit 𝒪 U J 𝒪τ α M).f n =
      (_root_.ModuleCat.extendRestrictScalarsAdj
        (coefficientMap 𝒪 U J 𝒪τ α)).unit.app (M.X n) ≫
      (scalarRestriction 𝒪 U J 𝒪τ α).map
        (((sheafificationUnit U J 𝒪τ).app
          ((PresheafOfModules.SameSiteTensorExtension.functor
            (sliceCoefficients 𝒪 U J 𝒪τ α)).obj
              ((constantModules U (𝒪.obj (op U))).obj (M.X n)))).app
                (op (Over.mk (𝟙 U)))) := rfl

private abbrev sliceSite := (RingedSite.ofCommRingSheaf J 𝒪τ).localization U

private abbrev localization :
    CochainComplex (RingedSite.ModuleCat.{max u v} (sliceSite U J 𝒪τ)) ℤ ⥤
      ModuleDerived.{max u v} (sliceSite U J 𝒪τ) :=
  @DerivedCategory.Q _ _ _ (moduleCat_hasDerivedCategory (sliceSite U J 𝒪τ))

private def derivedSectionsUnit :
    (evaluation U J 𝒪τ).mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex (_root_.ModuleCat.{max u v}
        (𝒪τ.obj.obj (op U))) ℤ ⥤ _) ⟶
      localization U J 𝒪τ ⋙
        moduleSectionsDerived.{max u v} (sliceSite U J 𝒪τ) (Over.mk (𝟙 U)) :=
  @Functor.RightDerived.Homotopy.cochainUnit
    _ _ _ (moduleCat_hasDerivedCategory (sliceSite U J 𝒪τ))
    _ _ _ inferInstance (evaluation U J 𝒪τ) inferInstance
    (@Functor.KInjectiveModel.Homotopy.hasRightDerived
      _ _ _ _ _ _ inferInstance (evaluation U J 𝒪τ) inferInstance
      inferInstance (moduleCat_hasDerivedCategory (sliceSite U J 𝒪τ)))

/-- The canonical morphism from a coefficient complex to derived sections of its associated
slice complex, retaining the action of the original section ring. -/
def comparison (M : CochainComplex (_root_.ModuleCat (𝒪.obj (op U))) ℤ) :
    DerivedCategory.Q.obj M ⟶
      (scalarRestriction 𝒪 U J 𝒪τ α).mapDerivedCategory.obj
        ((moduleSectionsDerived.{max u v} (sliceSite U J 𝒪τ) (Over.mk (𝟙 U))).obj
          ((localization U J 𝒪τ).obj (associatedComplex 𝒪 U J 𝒪τ α M))) :=
  DerivedCategory.Q.map (unit 𝒪 U J 𝒪τ α M) ≫
    (scalarRestriction 𝒪 U J 𝒪τ α).mapDerivedCategoryFactors.inv.app
      (((evaluation U J 𝒪τ).mapHomologicalComplex (up ℤ)).obj
        (associatedComplex 𝒪 U J 𝒪τ α M)) ≫
    (scalarRestriction 𝒪 U J 𝒪τ α).mapDerivedCategory.map
      ((derivedSectionsUnit U J 𝒪τ).app (associatedComplex 𝒪 U J 𝒪τ α M))

end RingedSite.Hom.TensorSections
