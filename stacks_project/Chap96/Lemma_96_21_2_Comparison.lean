module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Preadditive.Injective.Resolution.Map
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import stacks_project.Chap96.Lemma_96_21_2_Presheaf

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

/-- Evaluating cocontinuous abelian pushforward at `y` is the comma-limit of the
underlying presheaf. -/
def pushforwardEvalIsoRanLimit
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    ((abelianPushforward f τ).obj J).obj.obj (op y) ≅
      limit
        (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj) :=
  ((toCartesianBasedFunctor f).toFunctor.op.ranObjObjIsoLimit J.obj (op y))

/-- The comma functor sending an object of the Yoneda 2-fibre product to the corresponding
structured arrow for the cartesian total functor of `f`. -/
def toCartesianStructuredArrow (y : Y.total) :
    (yonedaFibreProduct f (fiberObj y)).totalᵒᵖ ⥤
      StructuredArrow (op y) (toCartesianBasedFunctor f).toFunctor.op :=
  yonedaFibreProduct.toStructuredArrow f (fiberObj y)

/-- Reindexing the Ran comma diagram along `toCartesianStructuredArrow` recovers the
inverse image along `pr`. -/
def yonedaFibreProduct_limitReindexHom
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    limit (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj) ⟶
      limit
        ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op ⋙
          J.obj) :=
  limit.pre
      (StructuredArrow.proj (op y) (toCartesianBasedFunctor f).toFunctor.op ⋙ J.obj)
      (toCartesianStructuredArrow f y)

/-- The reindexing map of the Ran comma diagram is an isomorphism. -/
instance yonedaFibreProduct_limitReindexHom_isIso
    (J : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (y : Y.total) :
    IsIso (yonedaFibreProduct_limitReindexHom f τ J y) :=
  sorry

/-- Reindexing the Ran comma diagram along `toCartesianStructuredArrow` recovers the
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
  pushforwardEvalIsoRanLimit f τ J y ≪≫
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

/-- Inverse image along `pr` preserves injective objects, so it sends injective
resolutions to injective resolutions. -/
instance abelianInverseImage_preservesInjectiveObjects_eval (y : Y.total) :
    ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        (X.associatedTopology τ)).PreservesInjectiveObjects :=
  sorry

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

/-- The Hom functor corepresented by the constant integer sheaf on a Yoneda 2-fibre
product. -/
abbrev fibreProductHomFunctor (y : Y.total) :
    Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op (constantIntegerSheaf.{u + 1, u, u + 1}
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))

/-- The fibre-product Hom functor is additive. -/
instance fibreProductHomFunctor.instAdditive (y : Y.total) :
    (fibreProductHomFunctor f τ y).Additive :=
  inferInstance

/-- Morphisms from the constant integer sheaf compute global sections on a Yoneda
2-fibre product. -/
def fibreProductHomIsoGamma (y : Y.total) :
    fibreProductHomFunctor f τ y ≅
      Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F ↦
      (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
          (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
          F).toAddCommGrpIso.symm)
    sorry

variable [∀ y : Y.total,
    HasSheafify (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    HasExt.{u + 1}
      (Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1})]

/-- Homology of the corepresented Hom complex of an injective resolution is `Ext` from the
constant integer sheaf. -/
def fibreProductHomologyExtIso (y : Y.total)
    {F : Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (i : ℕ) :
    (((fibreProductHomFunctor f τ y).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).homology (Int.ofNat i) ≅
      AddCommGrpCat.of
        (Ext (constantIntegerSheaf.{u + 1, u, u + 1}
            (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)) F i) :=
  HomologicalComplex.homologyMapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun n ↦
          (Cochain.fromSingleEquiv (zero_add n) :
              Cochain
                ((CochainComplex.singleFunctor _ 0).obj
                  (constantIntegerSheaf.{u + 1, u, u + 1}
                    (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))
                I.cochainComplex n ≃+
              (constantIntegerSheaf.{u + 1, u, u + 1}
                  (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) ⟶
                I.cochainComplex.X n)).symm.toAddCommGrpIso)
        sorry)
      (Int.ofNat i) ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1}
                (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))
            I.cochainComplex (Int.ofNat i)).toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1}
                (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))
            I.cochainComplex (Int.ofNat i)).symm.toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry } ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1}
                  (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)) F i ≃+
              CohomologyClass
                ((CochainComplex.singleFunctor _ 0).obj
                  (constantIntegerSheaf.{u + 1, u, u + 1}
                    (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))
                I.cochainComplex i).symm.toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1}
                  (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)) F i ≃+
              CohomologyClass
                ((CochainComplex.singleFunctor _ 0).obj
                  (constantIntegerSheaf.{u + 1, u, u + 1}
                    (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)))
                I.cochainComplex i).toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Global cohomology on a Yoneda 2-fibre product is derived global sections. -/
def fibreProductFunctorHIsoGammaRightDerived (y : Y.total) (i : ℕ)
    (F : Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}) :
    (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj F ≅
      ((Sheaf.Γ (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
            AddCommGrpCat.{u + 1}).rightDerived i).obj F :=
  (Iso.refl
      ((Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
        F) :
      (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
          F ≅
        AddCommGrpCat.of
          (Ext (constantIntegerSheaf.{u + 1, u, u + 1}
              (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)) F i)) ≪≫
    (fibreProductHomologyExtIso f τ y (injectiveResolution F) i).symm ≪≫
    (InjectiveResolution.RightDerived.homologyIso (injectiveResolution F)
      (fibreProductHomFunctor f τ y) i) ≪≫
    (CategoryTheory.NatIso.rightDerived (fibreProductHomIsoGamma f τ y) i).app F

/-- Objectwise homology of `f_* I` at `y` is `H^i_τ` of `pr⁻¹ F`. -/
def pushforwardResolutionEvalHomologyIsoFibreProductCohomology
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) (y : Y.total) :
    ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
        (pushforwardResolutionPresheafComplex f τ F)).obj (op y) ≅
      fibreProductCohomology f τ F i y :=
  pushforwardResolutionEvalHomologyIsoGammaRightDerived f τ F i y ≪≫
    (fibreProductFunctorHIsoGammaRightDerived f τ y i
      (abelianInverseImage f τ y F)).symm

/-- The presheaf sending an object `y` of `Y` to
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`. -/
def higherDirectImagePresheaf
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := fibreProductCohomology f τ F i y.unop
  map {y y'} φ :=
    (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y.unop).inv ≫
      ((homologyFunctor (Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) i).obj
          (pushforwardResolutionPresheafComplex f τ F)).map φ ≫
      (pushforwardResolutionEvalHomologyIsoFibreProductCohomology f τ F i y'.unop).hom
  map_id := sorry
  map_comp := sorry

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
def sheafify_higherDirectImagePresheaf
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
    (higherDirectImagePresheaf f τ F i)

/-- Sheafification of the fibre-product cohomology presheaf is `presheafToSheaf` of
that presheaf. -/
theorem sheafify_higherDirectImagePresheaf_eq
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafify_higherDirectImagePresheaf f τ F i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
        (higherDirectImagePresheaf f τ F i) :=
  rfl

/-- Identification of `R^i f_* F` with sheafification of the fibre-product cohomology
presheaf. -/
def sheafify_higherDirectImagePresheafIso_composite
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafify_higherDirectImagePresheaf f τ F i ≅ higherDirectImage f τ F i :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
      (pushforwardResolutionHomologyPresheafIso f τ F i).symm ≪≫
    (pushforwardResolutionHomologySheafIso f τ F i).symm ≪≫
    ((injectiveResolution F).isoRightDerivedObj (abelianPushforward f τ) i).symm

/-- The identification `R^i f_* F ≅` sheafification of the fibre-product cohomology
presheaf is the injective-resolution composite with the homology-to-cohomology
comparison. -/
theorem sheafify_higherDirectImagePresheafIso_composite_spec
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafify_higherDirectImagePresheafIso_composite f τ F i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
          (pushforwardResolutionHomologyPresheafIso f τ F i).symm ≪≫
        (pushforwardResolutionHomologySheafIso f τ F i).symm ≪≫
        ((injectiveResolution F).isoRightDerivedObj (abelianPushforward f τ) i).symm :=
  sorry

variable (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
variable [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    ∀ P : (yonedaFibreProduct f (fiberObj y)).totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op.HasLeftKanExtension
        P]

/-- Forgetting module structure identifies inverse image of `G` along `pr` with abelian
inverse image of `toSheaf G`. -/
def moduleInverseImage_toSheafIso (y : Y.total) :
    (SheafOfModules.toSheaf
        (associatedStructureSheaf (yonedaFibreProduct f (fiberObj y) : GroupoidsOver S)
          τ)).obj
      (moduleInverseImage f τ y G) ≅
      abelianInverseImage f τ y
        ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) :=
  (associatedModuleInverseImage_underlyingIso
      (yonedaFibreProduct.pr f (fiberObj y)) τ).app G

/-- Fibre-product module cohomology is abelian cohomology of `toSheaf (pr⁻¹ G)`. -/
def fibreProductModuleCohomologyIsoAbelian (y : Y.total) (i : ℕ) :
    fibreProductModuleCohomology f τ i G y ≅
      fibreProductCohomology f τ
        ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i y :=
  (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).mapIso
    (moduleInverseImage_toSheafIso f τ G y)

/-- The presheaf sending an object `y` of `Y` to
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ G)` for a sheaf of modules `G`. -/
def higherDirectImageModulePresheaf (i : ℕ) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj y := fibreProductModuleCohomology f τ i G y.unop
  map {y y'} φ :=
    (fibreProductModuleCohomologyIsoAbelian f τ G y.unop i).hom ≫
      (higherDirectImagePresheaf f τ
          ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i).map φ ≫
      (fibreProductModuleCohomologyIsoAbelian f τ G y'.unop i).inv
  map_id := sorry
  map_comp := sorry

/-- Evaluating the module cohomology presheaf at `y` is
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ G)`. -/
theorem higherDirectImageModulePresheaf_obj (i : ℕ) (y : Y.total) :
    (higherDirectImageModulePresheaf f τ G i).obj (op y) =
      fibreProductModuleCohomology f τ i G y :=
  rfl

/-- Sheafification of the module-coefficient fibre-product cohomology presheaf. -/
def sheafify_higherDirectImageModulePresheaf (i : ℕ) :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
    (higherDirectImageModulePresheaf f τ G i)

/-- The module cohomology presheaf is the abelian cohomology presheaf of `toSheaf G`. -/
def higherDirectImageModulePresheafIsoAbelian (i : ℕ) :
    higherDirectImageModulePresheaf f τ G i ≅
      higherDirectImagePresheaf f τ
        ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i :=
  NatIso.ofComponents
    (fun y ↦ fibreProductModuleCohomologyIsoAbelian f τ G y.unop i)
    sorry

/-- Forgetting module structure after `R^i f_*` on modules recovers the abelian
higher direct image of `toSheaf G`. -/
def higherDirectImageModule_toSheafIso (i : ℕ) :
    (SheafOfModules.toSheaf (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) ≅
      higherDirectImage f τ
        ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i :=
  (Functor.RightDerived.postcompObjIso (modulePushforward f τ)
        (SheafOfModules.toSheaf (associatedStructureSheaf Y τ)) i G).symm ≪≫
    (NatIso.rightDerived (modulePushforward_toSheafIso f τ) i).app G ≪≫
    Functor.RightDerived.precompObjIso
      (SheafOfModules.toSheaf (associatedStructureSheaf X τ))
      (abelianPushforward f τ) i G

/-- Identification of the underlying abelian sheaf of `R^i f_* G` with
sheafification of the module-coefficient fibre-product cohomology assignment. -/
def sheafify_higherDirectImageModulePresheafIso_composite (i : ℕ) :
    sheafify_higherDirectImageModulePresheaf f τ G i ≅
      (SheafOfModules.toSheaf (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) :=
  (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
      (higherDirectImageModulePresheafIsoAbelian f τ G i) ≪≫
    sheafify_higherDirectImagePresheafIso_composite f τ
      ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i ≪≫
    (higherDirectImageModule_toSheafIso f τ G i).symm

/-- The module-coefficient identification is sheafification of fibre-product cohomology
of `pr⁻¹ G`, compared with the abelian identification of `toSheaf G` and the
forgetful comparison of module and abelian higher direct images. -/
theorem sheafify_higherDirectImageModulePresheafIso_composite_spec (i : ℕ) :
    sheafify_higherDirectImageModulePresheafIso_composite f τ G i =
      (presheafToSheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}).mapIso
          (higherDirectImageModulePresheafIsoAbelian f τ G i) ≪≫
        sheafify_higherDirectImagePresheafIso_composite f τ
          ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) i ≪≫
        (higherDirectImageModule_toSheafIso f τ G i).symm :=
  sorry

end AlgebraicGeometry.GroupoidsOver
