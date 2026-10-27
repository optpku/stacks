/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cohomology.FibreProduct
public import ReasLib.CategoryTheory.Sites.GlobalSections.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.Resolution.ExactMap

/-!
# Injective-resolution comparison for higher direct images

`R^i f_* F` is computed from `f_*` of an injective resolution. Objectwise homology
of that complex at `y` is `H^i_τ` of `pr⁻¹ F` on the Yoneda 2-fibre product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open FiberedCategoryOver.Groupoids Functor HomologicalComplex Opposite ComplexShape
open CochainComplex.HomComplex
open scoped Bicategory

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `isoRightDerivedObj` and Additive instances on `toSheaf`/module pushforward.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]

/-- Sheafification of abelian presheaves on the associated `τ`-site of `Y` preserves
homology. -/
instance associatedPresheafToSheaf_preservesHomology :
    (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).PreservesHomology :=
  sorry

/-- The sheaf complex obtained by applying `f_*` to a chosen injective resolution of
`F`. -/
def pushforwardResolutionComplex
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    HomologicalComplex (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((abelianPushforward f τ).mapHomologicalComplex (up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- The underlying presheaf complex of `pushforwardResolutionComplex`. -/
def pushforwardResolutionPresheafComplex
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    HomologicalComplex (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((sheafToPresheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (up ℕ)).obj (pushforwardResolutionComplex f τ F)

/-- Sheafification of the underlying presheaf complex recovers the sheaf complex of
`f_* I`. -/
def pushforwardResolutionComplexSheafifyIso
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    pushforwardResolutionComplex f τ F ≅
      ((presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj (pushforwardResolutionPresheafComplex f τ F) :=
  (Functor.mapHomologicalComplexIdIso
      (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℕ)).symm.app
      (pushforwardResolutionComplex f τ F) ≪≫
    (NatIso.mapHomologicalComplex
        (sheafificationNatIso (Y.associatedTopology τ) AddCommGrpCat.{u + 1})
        (up ℕ)).app (pushforwardResolutionComplex f τ F) ≪≫
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (sheafToPresheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} ⋙
            presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}))
        (up ℕ)).symm.app (pushforwardResolutionComplex f τ F)

/-- Homology of `f_* I` as a sheaf is the sheafification of the objectwise homology
presheaf. -/
def pushforwardResolutionHomologySheafIso
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (homologyFunctor (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℕ) i).obj
        (pushforwardResolutionComplex f τ F) ≅
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
        ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
          (pushforwardResolutionPresheafComplex f τ F)) :=
  (homologyFunctor (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℕ) i).mapIso
      (pushforwardResolutionComplexSheafifyIso f τ F) ≪≫
    (pushforwardResolutionPresheafComplex f τ F).mapHomologyIso
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) i

/-- Reindexing the Ran comma diagram along the Yoneda structured-arrow functor recovers the
inverse image along `pr`. -/
def yonedaFibreProduct_limitReindexHom
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    limit (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj) ⟶
      limit
        ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op ⋙
          J.obj) :=
  limit.pre
    (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj)
    (yonedaFibreProduct.toStructuredArrow f (fiberObj y))

/-- The reindexing map of the Ran comma diagram is an isomorphism. -/
instance yonedaFibreProduct_limitReindexHom_isIso
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    IsIso (yonedaFibreProduct_limitReindexHom f τ J y) :=
  sorry

/-- Reindexing the Ran comma diagram along the Yoneda structured-arrow functor recovers the
inverse image along `pr`. -/
def yonedaFibreProduct_limitReindexIso
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    limit (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj) ≅
      limit
        ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op ⋙
          J.obj) :=
  asIso (yonedaFibreProduct_limitReindexHom f τ J y)

/-- Underived evaluation of `f_* J` at `y` is global sections of `pr⁻¹ J`. -/
def pushforwardEvalIsoGamma
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    ((abelianPushforward f τ).obj J).obj.obj (op y) ≅
      (Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
          AddCommGrpCat.{u + 1}).obj
        (abelianInverseImage f τ y J) :=
  ((toCartesianBasedFunctor f).toFunctor.op.ranObjObjIsoLimit J.obj (op y)) ≪≫
    yonedaFibreProduct_limitReindexIso f τ J y ≪≫
    (Sheaf.ΓNatIsoLim
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1}).symm.app
      (abelianInverseImage f τ y J)

/-- Degreewise underived comparison of `f_* I` with global sections of `pr⁻¹ I`. -/
def pushforwardResolutionEvalIsoGammaComplex
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    (((evaluation Y.totalᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)).mapHomologicalComplex
        (up ℕ)).obj
      (pushforwardResolutionPresheafComplex f τ F) ≅
      ((Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
            AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj
        ((((toCartesianBasedFunctor
                (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
              AddCommGrpCat.{u + 1}
              (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
              (X.associatedTopology τ)).mapHomologicalComplex
            (up ℕ)).obj
          (injectiveResolution F).cocomplex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ pushforwardEvalIsoGamma f τ ((injectiveResolution F).cocomplex.X n) y)
    sorry

variable [hX : AlgebraicStack X] [hY : AlgebraicStack Y]

/-- Objectwise homology of `f_* I` at `y` is derived global sections of `pr⁻¹ F`. -/
def pushforwardResolutionEvalHomologyIsoGammaRightDerived
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) (y : Y.total) :
    ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
        (pushforwardResolutionPresheafComplex f τ F)).obj (op y) ≅
      ((Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
            AddCommGrpCat.{u + 1}).rightDerived i).obj
        (abelianInverseImage f τ y F) :=
  ((pushforwardResolutionPresheafComplex f τ F).mapHomologyIso
        ((evaluation Y.totalᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)) i).symm ≪≫
    (homologyFunctor AddCommGrpCat.{u + 1} (up ℕ) i).mapIso
      (pushforwardResolutionEvalIsoGammaComplex f τ F y) ≪≫
    ((((toCartesianBasedFunctor
            (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
            AddCommGrpCat.{u + 1}
            (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
            (X.associatedTopology τ)).mapInjectiveResolution
          (injectiveResolution F)).isoRightDerivedObj
        (Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
          AddCommGrpCat.{u + 1})
        i).symm

variable [∀ y : Y.total,
    HasSheafify (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    HasExt.{u + 1}
      (Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1})]

/-- Objectwise homology of `f_* I` at `y` is `H^i_τ` of `pr⁻¹ F`. -/
def pushforwardResolutionEvalHomologyIsoFibreProductCohomology
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) (y : Y.total) :
    ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
        (pushforwardResolutionPresheafComplex f τ F)).obj (op y) ≅
      fibreProductCohomology f τ F i y :=
  pushforwardResolutionEvalHomologyIsoGammaRightDerived f τ F i y ≪≫
    (Sheaf.functorHIsoGammaRightDerived
      (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i
      (abelianInverseImage f τ y F)).symm

/-- Cohomology restriction is transport of the homology presheaf restriction map. -/
def higherDirectImagePresheafMap
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ)
    {y y' : Y.totalᵒᵖ} (φ : y ⟶ y') :
    fibreProductCohomology f τ F i y.unop ⟶ fibreProductCohomology f τ F i y'.unop :=
    (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y.unop).inv ≫
      ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
          (pushforwardResolutionPresheafComplex f τ F)).map φ ≫
      (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y'.unop).hom

/-- Transported cohomology restriction preserves identities. -/
theorem higherDirectImagePresheafMap_id
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) (y : Y.totalᵒᵖ) :
    higherDirectImagePresheafMap f τ F i (𝟙 y) =
      𝟙 (fibreProductCohomology f τ F i y.unop) := sorry

/-- Transported cohomology restriction preserves composition. -/
theorem higherDirectImagePresheafMap_comp
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ)
    {y y' y'' : Y.totalᵒᵖ} (φ : y ⟶ y') (ψ : y' ⟶ y'') :
    higherDirectImagePresheafMap f τ F i (φ ≫ ψ) =
      higherDirectImagePresheafMap f τ F i φ ≫ higherDirectImagePresheafMap f τ F i ψ := sorry

/-- The presheaf of cohomology of inverse images on Yoneda fibre products. -/
def higherDirectImagePresheaf
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := fibreProductCohomology f τ F i y.unop
  map φ := higherDirectImagePresheafMap f τ F i φ
  map_id := higherDirectImagePresheafMap_id f τ F i
  map_comp := higherDirectImagePresheafMap_comp f τ F i

/-- The cohomology presheaf restriction is the specified homology conjugation. -/
theorem higherDirectImagePresheaf_map
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ)
    {y y' : Y.totalᵒᵖ} (φ : y ⟶ y') :
    (higherDirectImagePresheaf f τ F i).map φ =
    (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y.unop).inv ≫
      ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
          (pushforwardResolutionPresheafComplex f τ F)).map φ ≫
      (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y'.unop).hom := rfl

/-- Evaluating the fibre-product cohomology presheaf at `y` is
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`. -/
theorem higherDirectImagePresheaf_obj
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ)
    (y : Y.total) :
    (higherDirectImagePresheaf f τ F i).obj (op y) = fibreProductCohomology f τ F i y :=
  rfl

/-- The objectwise homology presheaf of `f_* I` is the fibre-product cohomology presheaf. -/
def pushforwardResolutionHomologyPresheafIso
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
        (pushforwardResolutionPresheafComplex f τ F) ≅
      higherDirectImagePresheaf f τ F i :=
  NatIso.ofComponents
    (fun y ↦
      pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y.unop)
    sorry

/-- Sheafification of the fibre-product cohomology presheaf. -/
def sheafifyHigherDirectImagePresheaf
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
    (higherDirectImagePresheaf f τ F i)

/-- Sheafification of the fibre-product cohomology presheaf is `presheafToSheaf` of
that presheaf. -/
theorem sheafifyHigherDirectImagePresheaf_eq
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafifyHigherDirectImagePresheaf f τ F i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
        (higherDirectImagePresheaf f τ F i) :=
  rfl

/-- Identification of `R^i f_* F` with sheafification of the fibre-product cohomology
presheaf. -/
def sheafifyHigherDirectImagePresheafIso
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafifyHigherDirectImagePresheaf f τ F i ≅ higherDirectImage f τ F i :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
      (pushforwardResolutionHomologyPresheafIso f τ F i).symm ≪≫
    (pushforwardResolutionHomologySheafIso f τ F i).symm ≪≫
    ((injectiveResolution F).isoRightDerivedObj (abelianPushforward f τ) i).symm

/-- The identification `R^i f_* F ≅` sheafification of the fibre-product cohomology
presheaf is the injective-resolution composite with the homology-to-cohomology
comparison. -/
theorem sheafifyHigherDirectImagePresheafIso_spec
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafifyHigherDirectImagePresheafIso f τ F i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
          (pushforwardResolutionHomologyPresheafIso f τ F i).symm ≪≫
        (pushforwardResolutionHomologySheafIso f τ F i).symm ≪≫
        ((injectiveResolution F).isoRightDerivedObj (abelianPushforward f τ) i).symm :=
  rfl

variable (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
variable [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    ∀ P : (yonedaFibreProduct f (fiberObj y)).totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op.HasLeftKanExtension
        P]

/-- Fibre-product module cohomology is abelian cohomology of `toSheaf (pr⁻¹ G)`. -/
def fibreProductModuleCohomologyIsoAbelian (y : Y.total) (i : ℕ) :
    fibreProductModuleCohomology f τ i G y ≅
      fibreProductCohomology f τ
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i y :=
  (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).mapIso
    ((associatedModuleInverseImage_underlyingIso
      (yonedaFibreProduct.pr f (fiberObj y)) τ).app G)

/-- Module-coefficient restriction is conjugation by the additive cohomology comparison. -/
def higherDirectImageModulePresheafMap (i : ℕ) {y y' : Y.totalᵒᵖ} (φ : y ⟶ y') :
    fibreProductModuleCohomology f τ i G y.unop ⟶ fibreProductModuleCohomology f τ i G y'.unop :=
    (fibreProductModuleCohomologyIsoAbelian f τ G y.unop i).hom ≫
      (higherDirectImagePresheaf f τ
          ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i).map φ ≫
      (fibreProductModuleCohomologyIsoAbelian f τ G y'.unop i).inv

/-- Module-coefficient cohomology restriction preserves identities. -/
theorem higherDirectImageModulePresheafMap_id (i : ℕ) (y : Y.totalᵒᵖ) :
    higherDirectImageModulePresheafMap f τ G i (𝟙 y) =
      𝟙 (fibreProductModuleCohomology f τ i G y.unop) := sorry

/-- Module-coefficient cohomology restriction preserves composition. -/
theorem higherDirectImageModulePresheafMap_comp (i : ℕ)
    {y y' y'' : Y.totalᵒᵖ} (φ : y ⟶ y') (ψ : y' ⟶ y'') :
    higherDirectImageModulePresheafMap f τ G i (φ ≫ ψ) =
      higherDirectImageModulePresheafMap f τ G i φ ≫
        higherDirectImageModulePresheafMap f τ G i ψ := sorry

/-- The presheaf of module-coefficient cohomology on Yoneda fibre products. -/
def higherDirectImageModulePresheaf (i : ℕ) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := fibreProductModuleCohomology f τ i G y.unop
  map φ := higherDirectImageModulePresheafMap f τ G i φ
  map_id := higherDirectImageModulePresheafMap_id f τ G i
  map_comp := higherDirectImageModulePresheafMap_comp f τ G i

/-- Module-coefficient restriction has the specified additive comparison formula. -/
theorem higherDirectImageModulePresheaf_map (i : ℕ) {y y' : Y.totalᵒᵖ} (φ : y ⟶ y') :
    (higherDirectImageModulePresheaf f τ G i).map φ =
    (fibreProductModuleCohomologyIsoAbelian f τ G y.unop i).hom ≫
      (higherDirectImagePresheaf f τ
          ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i).map φ ≫
      (fibreProductModuleCohomologyIsoAbelian f τ G y'.unop i).inv := rfl

/-- Evaluating the module cohomology presheaf at `y` is
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ G)`. -/
theorem higherDirectImageModulePresheaf_obj (i : ℕ) (y : Y.total) :
    (higherDirectImageModulePresheaf f τ G i).obj (op y) =
      fibreProductModuleCohomology f τ i G y :=
  rfl

/-- Sheafification of the module-coefficient fibre-product cohomology presheaf. -/
def sheafifyHigherDirectImageModulePresheaf (i : ℕ) :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
    (higherDirectImageModulePresheaf f τ G i)

/-- The module cohomology presheaf is the abelian cohomology presheaf of `toSheaf G`. -/
def higherDirectImageModulePresheafIsoAbelian (i : ℕ) :
    higherDirectImageModulePresheaf f τ G i ≅
      higherDirectImagePresheaf f τ
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i :=
  NatIso.ofComponents
    (fun y ↦ fibreProductModuleCohomologyIsoAbelian f τ G y.unop i)
    sorry

/-- Exact forgetting of module structure sends a module resolution to a complex
with a canonical comparison to an additive injective resolution. -/
def moduleToSheafResolutionComparison :
    ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).mapHomologicalComplex (up ℕ)).obj
        (injectiveResolution G).cocomplex ⟶
      (injectiveResolution
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G)).cocomplex :=
  InjectiveResolution.ExactMap.map
    (SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)) (injectiveResolution G)
    (injectiveResolution ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G))

/-- Applying additive pushforward to the exact resolution comparison induces a
morphism from the derived composite to the additive higher direct image. -/
def moduleToSheafRightDerivedHom (i : ℕ) :
    ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ) ⋙
        abelianPushforward f τ).rightDerived i).obj G ⟶
      higherDirectImage f τ
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i :=
  let L := SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)
  let P := abelianPushforward f τ
  let I := injectiveResolution G
  let J := injectiveResolution (L.obj G)
  (I.isoRightDerivedObj (L ⋙ P) i).hom ≫
    (homologyFunctor _ (up ℕ) i).map
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ P)) (up ℕ)).symm.app
          I.cocomplex).hom ≫
        (P.mapHomologicalComplex (up ℕ)).map (moduleToSheafResolutionComparison τ G)) ≫
    (J.isoRightDerivedObj P i).inv

/-- The underlying module higher direct image maps to the additive higher direct
image through exact forgetting and the pushforward comparison. -/
def higherDirectImageModule_toSheafHom (i : ℕ) :
    (SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) ⟶
      higherDirectImage f τ
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i :=
  (Functor.RightDerived.postcompObjIso (modulePushforward f τ)
      (SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf Y τ)) i G).inv ≫
    ((NatIso.rightDerived (modulePushforward_toSheafIso f τ) i).app G).hom ≫
    moduleToSheafRightDerivedHom f τ G i

include hX hY in
/-- For algebraic stacks the exact-resolution comparison between module and
additive higher direct images is invertible. -/
@[instance] theorem higherDirectImageModule_toSheafHom_isIso (i : ℕ) :
    IsIso (higherDirectImageModule_toSheafHom f τ G i) := sorry

/-- The underlying additive sheaf of a module higher direct image is the additive
higher direct image of the underlying sheaf. -/
def higherDirectImageModule_toSheafIso (i : ℕ) :
    (SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) ≅
      higherDirectImage f τ
        ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i :=
  asIso (higherDirectImageModule_toSheafHom f τ G i)

/-- Identification of the underlying abelian sheaf of `R^i f_* G` with
sheafification of the module-coefficient fibre-product cohomology assignment. -/
def sheafifyHigherDirectImageModulePresheafIso (i : ℕ) :
    sheafifyHigherDirectImageModulePresheaf f τ G i ≅
      (SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
      (higherDirectImageModulePresheafIsoAbelian f τ G i) ≪≫
    sheafifyHigherDirectImagePresheafIso f τ
      ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i ≪≫
    (higherDirectImageModule_toSheafIso f τ G i).symm

/-- The module-coefficient identification is sheafification of fibre-product cohomology
of `pr⁻¹ G`, compared with the abelian identification of `toSheaf G` and the
forgetful comparison of module and abelian higher direct images. -/
theorem sheafifyHigherDirectImageModulePresheafIso_spec (i : ℕ) :
    sheafifyHigherDirectImageModulePresheafIso f τ G i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
          (higherDirectImageModulePresheafIsoAbelian f τ G i) ≪≫
        sheafifyHigherDirectImagePresheafIso f τ
          ((SheafOfModules.toSheaf.{u + 1} (associatedStructureSheaf X τ)).obj G) i ≪≫
        (higherDirectImageModule_toSheafIso f τ G i).symm :=
  rfl

end AlgebraicGeometry.GroupoidsOver
