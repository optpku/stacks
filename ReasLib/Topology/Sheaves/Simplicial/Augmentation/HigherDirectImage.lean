/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Preadditive.Injective.Resolution.Map
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Cohomology
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pullback
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pushforward

/-!
# Higher direct images of simplicial augmentations

The higher direct image `R^n a_* F` of an abelian sheaf along an augmentation is the
sheaf associated to the presheaf of Zariski cohomology groups of the restrictions of `F`
to the preimage simplicial spaces `Y ×_X V`.
-/

-- Private declaration justification (module visibility): export internal resolution bodies
-- so the exposed comparison can use them while their names remain private.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Functor CategoryTheory.Limits
open HomologicalComplex Opposite ComplexShape TopologicalSpace TopCat
open CochainComplex.HomComplex
open TopCat.Opens.Subspace
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)
variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
variable [∀ V : Opens X,
    HasSheafify (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}]
variable [∀ V : Opens X,
    HasExt.{u} (Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u})]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ AddCommGrpCat.{u},
    (constProjection X).op.HasPointwiseRightKanExtension F]
variable [HasInjectiveResolutions (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]

/-- Sheafification of abelian presheaves on `Opens X` preserves homology. -/
private instance opensPresheafToSheaf_preservesHomology :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
  sorry

/-- Evaluation of abelian presheaves on `Opens X` at an open preserves homology. -/
private instance opensEvaluation_preservesHomology (V : Opens X) :
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).PreservesHomology :=
  sorry

/-- Abelian sheaves on `(Y ×_X V)_Zar` have injective resolutions. -/
instance augmentationPreimage_hasInjectiveResolutions (V : Opens X) :
    HasInjectiveResolutions
      (Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}) :=
  sorry

/-- The sheaf complex obtained by applying `a_*` to a chosen injective resolution of `F`. -/
private def augmentationPushforwardResolutionComplex
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    HomologicalComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℕ) :=
  ((augmentationPushforward a).mapHomologicalComplex (up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- The underlying presheaf complex of `augmentationPushforwardResolutionComplex`. -/
private def augmentationPushforwardResolutionPresheafComplex
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    HomologicalComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (up ℕ)).obj (augmentationPushforwardResolutionComplex a F)

/-- Sheafification of the underlying presheaf complex recovers the sheaf complex of `a_* I`. -/
private def augmentationPushforwardResolutionComplexSheafifyIso
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    augmentationPushforwardResolutionComplex a F ≅
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℕ)).obj (augmentationPushforwardResolutionPresheafComplex a F) :=
  (Functor.mapHomologicalComplexIdIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℕ)).symm.app
      (augmentationPushforwardResolutionComplex a F) ≪≫
    (NatIso.mapHomologicalComplex
        (sheafificationNatIso (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (up ℕ)).app (augmentationPushforwardResolutionComplex a F) ≪≫
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
            presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
        (up ℕ)).symm.app (augmentationPushforwardResolutionComplex a F)

/-- Homology of `a_* I` as a sheaf is the sheafification of the objectwise homology presheaf. -/
private def augmentationPushforwardResolutionHomologySheafIso
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    (homologyFunctor (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℕ) n).obj
        (augmentationPushforwardResolutionComplex a F) ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
          (augmentationPushforwardResolutionPresheafComplex a F)) :=
  (homologyFunctor (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℕ) n).mapIso
      (augmentationPushforwardResolutionComplexSheafifyIso a F) ≪≫
    (augmentationPushforwardResolutionPresheafComplex a F).mapHomologyIso
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) n

/-- The Hom functor corepresented by the constant integer sheaf on `(Y ×_X V)_Zar`. -/
private abbrev augmentationPreimageHomFunctor (V : Opens X) :
    Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))

/-- The Hom functor from the constant integer sheaf on `(Y ×_X V)_Zar` is additive. -/
private instance augmentationPreimageHomFunctor.instAdditive (V : Opens X) :
    (augmentationPreimageHomFunctor a V).Additive :=
  inferInstance

/-- The component identification of morphisms from the constant integer sheaf with sections. -/
private def augmentationPreimageHomIsoGammaApp (V : Opens X)
    (F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}) :
    (augmentationPreimageHomFunctor a V).obj F ≅
      (Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).obj F :=
  (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (zariskiTopology (augmentationPreimage a V)) F).toAddCommGrpIso.symm

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The constant integer sheaf identification with global sections is natural in the sheaf. -/
private theorem augmentationPreimageHomIsoGamma_naturality (V : Opens X)
    {F G : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}} (f : F ⟶ G) :
    (augmentationPreimageHomFunctor a V).map f ≫ (augmentationPreimageHomIsoGammaApp a V G).hom =
      (augmentationPreimageHomIsoGammaApp a V F).hom ≫
        (Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).map f := by
  sorry

/-- Morphisms from the constant integer sheaf compute global sections on `(Y ×_X V)_Zar`. -/
private def augmentationPreimageHomIsoGamma (V : Opens X) :
    augmentationPreimageHomFunctor a V ≅
      Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (augmentationPreimageHomIsoGammaApp a V)
    (fun {F G} f ↦ augmentationPreimageHomIsoGamma_naturality a V f)

/-- The degreewise identification of the corepresented Hom complex with cochains. -/
private def augmentationPreimageHomComplexIsoApp (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (i : ℤ) :
    (((augmentationPreimageHomFunctor a V).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).X i ≅
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor _ 0).obj
          (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
        I.cochainComplex).X i :=
  (Cochain.fromSingleEquiv (zero_add i) :
      Cochain ((CochainComplex.singleFunctor _ 0).obj
          (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
        I.cochainComplex i ≃+
      (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V)) ⟶
        I.cochainComplex.X i)).symm.toAddCommGrpIso

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The degreewise Hom-complex identification commutes with differentials. -/
private theorem augmentationPreimageHomComplexIso_comm (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (i j : ℤ) (h : (up ℤ).Rel i j) :
    (augmentationPreimageHomComplexIsoApp a V I i).hom ≫
        (CochainComplex.HomComplex
          ((CochainComplex.singleFunctor _ 0).obj
            (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
          I.cochainComplex).d i j =
      (((augmentationPreimageHomFunctor a V).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).d i j ≫ (augmentationPreimageHomComplexIsoApp a V I j).hom := by
  sorry

/-- Applying Hom from the constant integer sheaf to an injective resolution gives the standard
Hom complex from the corresponding single complex. -/
private def augmentationPreimageHomComplexIso (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    ((augmentationPreimageHomFunctor a V).mapHomologicalComplex (up ℤ)).obj I.cochainComplex ≅
      CochainComplex.HomComplex
        ((CochainComplex.singleFunctor _ 0).obj
          (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
        I.cochainComplex :=
  Hom.isoOfComponents (augmentationPreimageHomComplexIsoApp a V I)
    (augmentationPreimageHomComplexIso_comm a V I)

/-- Homology of the standard Hom complex is the group of cohomology classes. -/
private def augmentationPreimageHomologyClassIso (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor _ 0).obj
          (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
        I.cochainComplex).homology (Int.ofNat n) ≅
      AddCommGrpCat.of
        (CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj
            (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
          I.cochainComplex (Int.ofNat n)) :=
  (homologyAddEquiv
      ((CochainComplex.singleFunctor _ 0).obj
        (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
      I.cochainComplex (Int.ofNat n)).toAddCommGrpIso

/-- Cohomology classes of a chosen injective resolution are the corresponding `Ext` group. -/
private def augmentationPreimageExtCohomologyClassIso (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    AddCommGrpCat.of
        (CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj
            (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))))
          I.cochainComplex n) ≅
      AddCommGrpCat.of
        (Ext (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))) F n) :=
  I.extAddEquivCohomologyClass.symm.toAddCommGrpIso

/-- Homology of the corepresented Hom complex of an injective resolution is `Ext` from the
constant integer sheaf. -/
private def augmentationPreimageHomologyExtIso (V : Opens X)
    {F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    (((augmentationPreimageHomFunctor a V).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).homology (Int.ofNat n) ≅
      AddCommGrpCat.of
        (Ext (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))) F n) :=
  HomologicalComplex.homologyMapIso (augmentationPreimageHomComplexIso a V I) (Int.ofNat n) ≪≫
    augmentationPreimageHomologyClassIso a V I n ≪≫
    augmentationPreimageExtCohomologyClassIso a V I n

/-- Global cohomology on `(Y ×_X V)_Zar` is derived global sections. -/
private def augmentationPreimageFunctorHIsoGammaRightDerived (V : Opens X) (n : ℕ)
    (F : Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}) :
    (Sheaf.functorH (zariskiTopology (augmentationPreimage a V)) n).obj F ≅
      ((Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).rightDerived n).obj
        F :=
  (Iso.refl ((Sheaf.functorH (zariskiTopology (augmentationPreimage a V)) n).obj F) :
      (Sheaf.functorH (zariskiTopology (augmentationPreimage a V)) n).obj F ≅
        AddCommGrpCat.of
          (Ext (constantIntegerSheaf (zariskiTopology (augmentationPreimage a V))) F n)) ≪≫
    (augmentationPreimageHomologyExtIso a V (injectiveResolution F) n).symm ≪≫
    (InjectiveResolution.RightDerived.homologyIso
      (injectiveResolution F) (augmentationPreimageHomFunctor a V) n) ≪≫
    (CategoryTheory.NatIso.rightDerived (augmentationPreimageHomIsoGamma a V) n).app F

/-- The comma object of `constProjection` over `V` given by the stage-`U.base` copy of `V`. -/
private def augmentationPreimageTopComma (V : Opens X)
    (U : zariskiSite (augmentationPreimage a V)) :
    StructuredArrow (op V) (constProjection X).op :=
  StructuredArrow.mk
    (op (𝟙 V) :
      op V ⟶
        (constProjection X).op.obj (op (DiagramOpens.ofOpens (constSpace X) U.base V)))

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The identity stage map carries an ambient preimage open into the full open preimage. -/
private theorem augmentationPreimageTopRestrict_mapsTo (V : Opens X)
    (U : zariskiSite (augmentationPreimage a V)) :
    Set.MapsTo (Y.map (𝟙 U.base)).hom
      ((augmentationPreimageSiteι a V).obj U).opens.carrier
      ((zariskiMap a).obj (DiagramOpens.ofOpens (constSpace X) U.base V)).opens.carrier := by
  sorry

/-- Restriction from `a_n⁻¹(V)` to an open of `(Y ×_X V)_n`, as a morphism of `Y_Zar`. -/
private def augmentationPreimageTopRestrict (V : Opens X)
    (U : zariskiSite (augmentationPreimage a V)) :
    (augmentationPreimageSiteι a V).obj U ⟶
      (zariskiMap a).obj (DiagramOpens.ofOpens (constSpace X) U.base V) :=
  DiagramOpens.homMk (𝟙 U.base) (augmentationPreimageTopRestrict_mapsTo a V U)

/-- The open of `Y ×_X V` corresponding to a `constProjection`-comma object over `V`. -/
private def augmentationCommaPreimageOpen (V : Opens X)
    (f : StructuredArrow (op V) (constProjection X).op) :
    zariskiSite (augmentationPreimage a V) :=
  DiagramOpens.ofOpens (augmentationPreimage a V) f.right.unop.base
    (preimageOpen ((Opens.map (a.app f.right.unop.base)).obj V)
      ((Opens.map (a.app f.right.unop.base)).obj f.right.unop.opens))

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The identity stage map carries a comma open into its ambient preimage open. -/
private theorem augmentationCommaRestrict_mapsTo (V : Opens X)
    (f : StructuredArrow (op V) (constProjection X).op) :
    Set.MapsTo (Y.map (𝟙 f.right.unop.base)).hom
      ((zariskiMap a).obj f.right.unop).opens.carrier
      ((augmentationPreimageSiteι a V).obj (augmentationCommaPreimageOpen a V f)).opens.carrier := by
  sorry

/-- Comparison in `Y_Zar` from `zariskiMap a` of a comma object to the corresponding open of
`(Y ×_X V)_Zar`. -/
private def augmentationCommaRestrict (V : Opens X)
    (f : StructuredArrow (op V) (constProjection X).op) :
    (zariskiMap a).obj f.right.unop ⟶
      (augmentationPreimageSiteι a V).obj (augmentationCommaPreimageOpen a V f) :=
  DiagramOpens.homMk (𝟙 f.right.unop.base) (augmentationCommaRestrict_mapsTo a V f)

/-- The Ran comma diagram computing `(a_* G)(V)`. -/
private abbrev augmentationPushforwardCommaDiagram (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    StructuredArrow (op V) (constProjection X).op ⥤ AddCommGrpCat.{u} :=
  StructuredArrow.proj (op V) (constProjection X).op ⋙
    (((zariskiMap a).sheafPushforwardContinuous AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G).obj

/-- The diagram of sections of `G` on opens of `(Y ×_X V)_Zar`. -/
private abbrev augmentationPreimageSectionsDiagram (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    (zariskiSite (augmentationPreimage a V))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((restrictAugmentationPreimage a V).obj G).obj

/-- The component from the comma limit to sections over a preimage open. -/
private def augmentationPushforwardCommaToPreimageConeApp (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (W : (zariskiSite (augmentationPreimage a V))ᵒᵖ) :=
  limit.π (augmentationPushforwardCommaDiagram a V G)
      (augmentationPreimageTopComma a V W.unop) ≫
    G.obj.map (op (augmentationPreimageTopRestrict a V W.unop))

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The comma-limit section components commute with restriction of preimage opens. -/
private theorem augmentationPushforwardCommaToPreimageCone_naturality (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    {U W : (zariskiSite (augmentationPreimage a V))ᵒᵖ} (f : U ⟶ W) :
    𝟙 _ ≫ augmentationPushforwardCommaToPreimageConeApp a V G W =
      augmentationPushforwardCommaToPreimageConeApp a V G U ≫
        (augmentationPreimageSectionsDiagram a V G).map f := by
  sorry

/-- The cone presenting the Ran limit of `a_* G` at `V` as sections on `(Y ×_X V)_Zar`. -/
private def augmentationPushforwardCommaToPreimageCone (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    Cone (augmentationPreimageSectionsDiagram a V G) where
  pt := limit (augmentationPushforwardCommaDiagram a V G)
  π :=
    { app := augmentationPushforwardCommaToPreimageConeApp a V G
      naturality := fun _ _ f ↦ augmentationPushforwardCommaToPreimageCone_naturality a V G f }

/-- The component from the preimage sections limit to a comma-diagram value. -/
private def augmentationPreimageToPushforwardCommaConeApp (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (f : StructuredArrow (op V) (constProjection X).op) :=
  limit.π (augmentationPreimageSectionsDiagram a V G)
      (op (augmentationCommaPreimageOpen a V f)) ≫
    G.obj.map (op (augmentationCommaRestrict a V f))

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The preimage-limit section components commute with comma-diagram morphisms. -/
private theorem augmentationPreimageToPushforwardCommaCone_naturality (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    {f g : StructuredArrow (op V) (constProjection X).op} (h : f ⟶ g) :
    𝟙 _ ≫ augmentationPreimageToPushforwardCommaConeApp a V G g =
      augmentationPreimageToPushforwardCommaConeApp a V G f ≫
        (augmentationPushforwardCommaDiagram a V G).map h := by
  sorry

/-- The cone presenting global sections on `(Y ×_X V)_Zar` as the Ran limit of `a_* G` at `V`. -/
private def augmentationPreimageToPushforwardCommaCone (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    Cone (augmentationPushforwardCommaDiagram a V G) where
  pt := limit (augmentationPreimageSectionsDiagram a V G)
  π :=
    { app := augmentationPreimageToPushforwardCommaConeApp a V G
      naturality := fun _ _ h ↦ augmentationPreimageToPushforwardCommaCone_naturality a V G h }

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The two section-limit comparison maps compose to the identity on the comma limit. -/
private theorem augmentationPushforwardLimitIsoRestrictLimit_hom_inv_id (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    limit.lift (augmentationPreimageSectionsDiagram a V G)
        (augmentationPushforwardCommaToPreimageCone a V G) ≫
      limit.lift (augmentationPushforwardCommaDiagram a V G)
        (augmentationPreimageToPushforwardCommaCone a V G) = 𝟙 _ := by
  sorry

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The two section-limit comparison maps compose to the identity on the preimage limit. -/
private theorem augmentationPushforwardLimitIsoRestrictLimit_inv_hom_id (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    limit.lift (augmentationPushforwardCommaDiagram a V G)
        (augmentationPreimageToPushforwardCommaCone a V G) ≫
      limit.lift (augmentationPreimageSectionsDiagram a V G)
        (augmentationPushforwardCommaToPreimageCone a V G) = 𝟙 _ := by
  sorry

/-- The Ran limit computing `(a_* G)(V)` is the limit of sections on `(Y ×_X V)_Zar`. -/
private def augmentationPushforwardLimitIsoRestrictLimit (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    limit (augmentationPushforwardCommaDiagram a V G) ≅
      limit (augmentationPreimageSectionsDiagram a V G) :=
  Iso.mk
    (limit.lift (augmentationPreimageSectionsDiagram a V G)
      (augmentationPushforwardCommaToPreimageCone a V G))
    (limit.lift (augmentationPushforwardCommaDiagram a V G)
      (augmentationPreimageToPushforwardCommaCone a V G))
    (augmentationPushforwardLimitIsoRestrictLimit_hom_inv_id a V G)
    (augmentationPushforwardLimitIsoRestrictLimit_inv_hom_id a V G)

/-- Underived evaluation of `a_* G` at `V` is global sections of the restriction of `G` to
`(Y ×_X V)_Zar`. -/
private def augmentationPushforwardEvalIsoGamma (V : Opens X)
    (G : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    (((augmentationPushforward a).obj G).obj.obj (op V)) ≅
      (Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).obj
        ((restrictAugmentationPreimage a V).obj G) :=
  ((constProjection X).op.ranObjObjIsoLimit
      (((zariskiMap a).sheafPushforwardContinuous AddCommGrpCat.{u}
          (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G).obj
      (op V)) ≪≫
    augmentationPushforwardLimitIsoRestrictLimit a V G ≪≫
    (Sheaf.ΓNatIsoLim (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).symm.app
      ((restrictAugmentationPreimage a V).obj G)

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- Evaluation of the pushed resolution and restricted global sections have compatible differentials. -/
private theorem augmentationPushforwardResolutionEvalIsoGammaComplex_comm
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (V : Opens X)
    (i j : ℕ) (h : (up ℕ).Rel i j) :
    (augmentationPushforwardEvalIsoGamma a V ((injectiveResolution F).cocomplex.X i)).hom ≫
        (((Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).mapHomologicalComplex
          (up ℕ)).obj
          (((restrictAugmentationPreimage a V).mapHomologicalComplex (up ℕ)).obj
            (injectiveResolution F).cocomplex)).d i j =
      ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex
          (up ℕ)).obj (augmentationPushforwardResolutionPresheafComplex a F)).d i j ≫
        (augmentationPushforwardEvalIsoGamma a V ((injectiveResolution F).cocomplex.X j)).hom := by
  sorry

/-- Degreewise underived comparison of the pushed injective resolution with global sections of
its restriction to `Y ×_X V`. -/
private def augmentationPushforwardResolutionEvalIsoGammaComplex
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (V : Opens X) :
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex
        (up ℕ)).obj (augmentationPushforwardResolutionPresheafComplex a F) ≅
      ((Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℕ)).obj
        (((restrictAugmentationPreimage a V).mapHomologicalComplex (up ℕ)).obj
          (injectiveResolution F).cocomplex) :=
  Hom.isoOfComponents
    (fun n ↦
      augmentationPushforwardEvalIsoGamma a V ((injectiveResolution F).cocomplex.X n))
    (augmentationPushforwardResolutionEvalIsoGammaComplex_comm a F V)

/-- Objectwise homology of `a_* I` at `V` is derived global sections of the restricted sheaf. -/
private def augmentationPushforwardResolutionEvalHomologyIsoGammaRightDerived
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) (V : Opens X) :
    ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
        (augmentationPushforwardResolutionPresheafComplex a F)).obj (op V) ≅
      ((Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}).rightDerived n).obj
        ((restrictAugmentationPreimage a V).obj F) :=
  ((augmentationPushforwardResolutionPresheafComplex a F).mapHomologyIso
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) n).symm ≪≫
    (homologyFunctor AddCommGrpCat.{u} (up ℕ) n).mapIso
      (augmentationPushforwardResolutionEvalIsoGammaComplex a F V) ≪≫
    (((restrictAugmentationPreimage a V).mapInjectiveResolution
          (injectiveResolution F)).isoRightDerivedObj
        (Sheaf.Γ (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}) n).symm

/-- Objectwise homology of `a_* I` at `V` is Zariski cohomology of the restricted sheaf. -/
private def augmentationPushforwardResolutionEvalHomologyIsoZariskiCohomology
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) (V : Opens X) :
    ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
        (augmentationPushforwardResolutionPresheafComplex a F)).obj (op V) ≅
      zariskiCohomology (augmentationPreimage a V) ((restrictAugmentationPreimage a V).obj F) n :=
  augmentationPushforwardResolutionEvalHomologyIsoGammaRightDerived a F n V ≪≫
    (augmentationPreimageFunctorHIsoGammaRightDerived a V n
      ((restrictAugmentationPreimage a V).obj F)).symm

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}] in
/-- The resolution homology comparison respects the cohomological restriction maps. -/
private theorem augmentationPushforwardResolutionHomologyPresheafIso_naturality
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ)
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
        (augmentationPushforwardResolutionPresheafComplex a F)).map f ≫
      (augmentationPushforwardResolutionEvalHomologyIsoZariskiCohomology a F n W.unop).hom =
      (augmentationPushforwardResolutionEvalHomologyIsoZariskiCohomology a F n V.unop).hom ≫
        (augmentationCohomologyPresheaf a F n).map f := by
  sorry

/-- The objectwise homology presheaf of `a_* I` is the augmentation cohomology presheaf. -/
private def augmentationPushforwardResolutionHomologyPresheafIso
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    (homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
        (augmentationPushforwardResolutionPresheafComplex a F) ≅
      augmentationCohomologyPresheaf a F n :=
  NatIso.ofComponents
    (fun V ↦
      augmentationPushforwardResolutionEvalHomologyIsoZariskiCohomology a F n V.unop)
    (fun {V W} f ↦ augmentationPushforwardResolutionHomologyPresheafIso_naturality a F n f)

/-- `R^n a_* F` is the sheafification of the objectwise homology of `a_* I`. -/
private def augmentationHigherDirectImageIsoHomologyPresheaf
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    (augmentationHigherDirectImageFunctor a n).obj F ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
          (augmentationPushforwardResolutionPresheafComplex a F)) :=
  (injectiveResolution F).isoRightDerivedObj (augmentationPushforward a) n ≪≫
    augmentationPushforwardResolutionHomologySheafIso a F n

/-- The sheafification of the homology presheaf of `a_* I` is the sheafification of the
augmentation cohomology presheaf. -/
private def sheafifiedHomologyPresheafIsoAugmentationCohomology
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((homologyFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℕ) n).obj
          (augmentationPushforwardResolutionPresheafComplex a F)) ≅
      sheafifiedAugmentationCohomology a F n :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
    (augmentationPushforwardResolutionHomologyPresheafIso a F n)

/-- For a simplicial space `Y`, an augmentation `a : Y ⟶ constSpace X`, and an
abelian sheaf `F` on `Y_Zar`, the higher direct image `R^n a_* F` is the sheaf on `X`
associated to the presheaf `V ↦ H^n((Y ×_X V)_Zar, F|_(Y ×_X V)_Zar)`. -/
def sheafifiedAugmentationCohomology_iso_higherDirectImage
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    sheafifiedAugmentationCohomology a F n ≅
      (augmentationHigherDirectImageFunctor a n).obj F :=
  (sheafifiedHomologyPresheafIsoAugmentationCohomology a F n).symm ≪≫
    (augmentationHigherDirectImageIsoHomologyPresheaf a F n).symm

/-- The higher-direct-image identification is the composite of the sheafified homology identification with
the injective-resolution computation of `R^n a_*`. -/
theorem sheafifiedAugmentationCohomology_iso_higherDirectImage_spec
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    sheafifiedAugmentationCohomology_iso_higherDirectImage a F n =
      (sheafifiedHomologyPresheafIsoAugmentationCohomology a F n).symm ≪≫
        (augmentationHigherDirectImageIsoHomologyPresheaf a F n).symm :=
  rfl

end CategoryTheory.SimplicialObject
