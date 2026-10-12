/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import stacks_project.Chap103.«103_15_2_1_Map»
public import stacks_project.Chap103.«103_15_2_1_FibreProduct»

/-!
# Higher direct images on lisse-étale and flat-fppf sites

Lemma 103.15.2 / tag 07AW: the higher direct image `R^p f'_* H` along the
restricted site functor of a smooth (resp. flat) morphism of algebraic stacks
is the sheaf associated to the cohomology of the primed pullback of `H` on the
primed fibre product `(V ×_{y, Y} X)'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Abelian CategoryTheory.Limits
open HomologicalComplex Opposite ComplexShape
open CochainComplex.HomComplex
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]

/-- Sheafification of abelian presheaves on the lisse-étale site of `Y` preserves homology. -/
instance lisseEtalePresheafToSheaf_preservesHomology :
    (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).PreservesHomology :=
  sorry

/-- Continuous pullback to a primed lisse-étale fibre product is additive. -/
instance lisseEtalePrimedPullbackFunctor.instAdditive
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    ((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).Additive :=
  sorry

/-- Continuous pullback to a primed lisse-étale fibre product preserves injective objects. -/
instance lisseEtalePrimedPullbackFunctor.instPreservesInjectiveObjects
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    ((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).PreservesInjectiveObjects :=
  sorry

/-- Continuous pullback to a primed lisse-étale fibre product preserves homology. -/
instance lisseEtalePrimedPullbackFunctor.instPreservesHomology
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    ((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).PreservesHomology :=
  sorry

/-- The abelian sheaf category on a primed lisse-étale fibre product has injective resolutions. -/
instance lisseEtalePrimed_hasInjectiveResolutions
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    HasInjectiveResolutions
      (Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}) :=
  sorry

/-- The sheaf complex obtained by applying `f'_*` to a chosen injective resolution of `H`. -/
def lisseEtalePushforwardResolutionComplex (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    HomologicalComplex (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((lisseEtalePushforward f).mapHomologicalComplex (up ℕ)).obj
    (injectiveResolution H).cocomplex

/-- The underlying presheaf complex of `lisseEtalePushforwardResolutionComplex`. -/
def lisseEtalePushforwardResolutionPresheafComplex (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    HomologicalComplex ((lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((sheafToPresheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (up ℕ)).obj (lisseEtalePushforwardResolutionComplex f H)

/-- Sheafification of the underlying presheaf complex recovers the sheaf complex of `f'_* I`. -/
def lisseEtalePushforwardResolutionComplexSheafifyIso (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    lisseEtalePushforwardResolutionComplex f H ≅
      ((presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj (lisseEtalePushforwardResolutionPresheafComplex f H) :=
  (Functor.mapHomologicalComplexIdIso
      (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}) (up ℕ)).symm.app
      (lisseEtalePushforwardResolutionComplex f H) ≪≫
    (NatIso.mapHomologicalComplex
        (sheafificationNatIso (lisseEtaleTopology Y) AddCommGrpCat.{u + 1})
        (up ℕ)).app (lisseEtalePushforwardResolutionComplex f H) ≪≫
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (sheafToPresheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1} ⋙
            presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}))
        (up ℕ)).symm.app (lisseEtalePushforwardResolutionComplex f H)

/-- Homology of `f'_* I` as a sheaf is the sheafification of the objectwise homology presheaf. -/
def lisseEtalePushforwardResolutionHomologySheafIso (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (homologyFunctor (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (lisseEtalePushforwardResolutionComplex f H) ≅
      (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).obj
        ((homologyFunctor ((lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
          (lisseEtalePushforwardResolutionPresheafComplex f H)) :=
  (homologyFunctor (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) p).mapIso
      (lisseEtalePushforwardResolutionComplexSheafifyIso f H) ≪≫
    (lisseEtalePushforwardResolutionPresheafComplex f H).mapHomologyIso
      (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}) p

/-- The Hom functor corepresented by the constant integer sheaf on a primed lisse-étale site. -/
abbrev lisseEtalePrimedHomFunctor (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))

/-- The primed lisse-étale Hom functor is additive. -/
instance lisseEtalePrimedHomFunctor.instAdditive
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    (lisseEtalePrimedHomFunctor f y).Additive :=
  inferInstance

/-- Morphisms from the constant integer sheaf compute global sections on a primed lisse-étale
fibre product. -/
def lisseEtalePrimedHomIsoGamma (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    lisseEtalePrimedHomFunctor f y ≅
      Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F ↦
      (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
        (lisseEtalePrimedTopology f y) F).toAddCommGrpIso.symm)
    sorry

/-- Homology of the corepresented Hom complex of an injective resolution is `Ext` from the
constant integer sheaf. -/
def lisseEtalePrimedHomologyExtIso (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    {F : Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (p : ℕ) :
    (((lisseEtalePrimedHomFunctor f y).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).homology (Int.ofNat p) ≅
      AddCommGrpCat.of
        (Ext (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)) F p) :=
  HomologicalComplex.homologyMapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun i ↦
          (Cochain.fromSingleEquiv (zero_add i) :
              Cochain ((CochainComplex.singleFunctor _ 0).obj
                  (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))
                I.cochainComplex i ≃+
              (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y) ⟶
                I.cochainComplex.X i)).symm.toAddCommGrpIso)
        sorry)
      (Int.ofNat p) ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))
            I.cochainComplex (Int.ofNat p)).toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))
            I.cochainComplex (Int.ofNat p)).symm.toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry } ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)) F p ≃+
                CohomologyClass
                  ((CochainComplex.singleFunctor _ 0).obj
                    (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))
                  I.cochainComplex p).symm.toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)) F p ≃+
                CohomologyClass
                  ((CochainComplex.singleFunctor _ 0).obj
                    (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)))
                  I.cochainComplex p).toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Global cohomology on a primed lisse-étale fibre product is derived global sections. -/
def lisseEtalePrimedFunctorHIsoGammaRightDerived (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) (p : ℕ)
    (F : Sheaf (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}) :
    (Sheaf.functorH (lisseEtalePrimedTopology f y) p).obj F ≅
      ((Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).rightDerived p).obj F :=
  (Iso.refl ((Sheaf.functorH (lisseEtalePrimedTopology f y) p).obj F) :
      (Sheaf.functorH (lisseEtalePrimedTopology f y) p).obj F ≅
        AddCommGrpCat.of
          (Ext (constantIntegerSheaf.{u + 1, u, u + 1} (lisseEtalePrimedTopology f y)) F p)) ≪≫
    (lisseEtalePrimedHomologyExtIso f y (injectiveResolution F) p).symm ≪≫
    (InjectiveResolution.RightDerived.homologyIso
      (injectiveResolution F) (lisseEtalePrimedHomFunctor f y) p) ≪≫
    (CategoryTheory.NatIso.rightDerived (lisseEtalePrimedHomIsoGamma f y) p).app F

/-- Reindexing the Ran comma diagram along `costructuredArrowOpEquivalence` recovers the primed
projection. -/
def lisseEtalePrimedLimitReindexIso (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (J : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    limit (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ J.obj) ≅
      limit ((lisseEtalePrimedPr f y).op ⋙ J.obj) :=
  (HasLimit.isoOfEquivalence
      (costructuredArrowOpEquivalence (lisseEtaleMap f) y)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)).symm

/-- Underived evaluation of cocontinuous pushforward at `y` is global sections of the primed
pullback. -/
def lisseEtalePushforwardEvalIsoGamma (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (J : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (((lisseEtalePushforward f).obj J).obj.obj (op y)) ≅
      (Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).obj
        (lisseEtalePrimedPullback f y J) :=
  ((lisseEtaleMap f).op.ranObjObjIsoLimit J.obj (op y)) ≪≫
    lisseEtalePrimedLimitReindexIso f y J ≪≫
    (Sheaf.ΓNatIsoLim (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).symm.app
      (lisseEtalePrimedPullback f y J)

/-- Degreewise underived comparison of the pushed injective resolution with global sections of
its primed pullback. -/
def lisseEtalePushforwardResolutionEvalIsoGammaComplex (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (y : lisseEtaleSite Y) :
    (((evaluation (lisseEtaleSite Y)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)).mapHomologicalComplex
        (up ℕ)).obj (lisseEtalePushforwardResolutionPresheafComplex f H) ≅
      ((Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj
        ((((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).mapHomologicalComplex
            (up ℕ)).obj (injectiveResolution H).cocomplex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      lisseEtalePushforwardEvalIsoGamma f y ((injectiveResolution H).cocomplex.X n))
    sorry

/-- Objectwise homology of `f'_* I` at `y` is derived global sections of `(pr')⁻¹ H`. -/
def lisseEtalePushforwardResolutionEvalHomologyIsoGammaRightDerived
    (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : lisseEtaleSite Y) :
    ((homologyFunctor ((lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (lisseEtalePushforwardResolutionPresheafComplex f H)).obj (op y) ≅
      ((Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}).rightDerived p).obj
        (lisseEtalePrimedPullback f y H) :=
  ((lisseEtalePushforwardResolutionPresheafComplex f H).mapHomologyIso
        ((evaluation (lisseEtaleSite Y)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)) p).symm ≪≫
    (homologyFunctor AddCommGrpCat.{u + 1} (up ℕ) p).mapIso
      (lisseEtalePushforwardResolutionEvalIsoGammaComplex f H y) ≪≫
    ((((lisseEtalePrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (lisseEtalePrimedTopology f y) (lisseEtaleTopology X)).mapInjectiveResolution
          (injectiveResolution H)).isoRightDerivedObj
        (Sheaf.Γ (lisseEtalePrimedTopology f y) AddCommGrpCat.{u + 1}) p).symm

/-- Objectwise homology of `f'_* I` at `y` is global cohomology of `(pr')⁻¹ H`. -/
def lisseEtalePushforwardResolutionEvalHomologyIsoPrimedH
    (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : lisseEtaleSite Y) :
    ((homologyFunctor ((lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (lisseEtalePushforwardResolutionPresheafComplex f H)).obj (op y) ≅
      AddCommGrpCat.of ((lisseEtalePrimedPullback f y H).H p) :=
  lisseEtalePushforwardResolutionEvalHomologyIsoGammaRightDerived f H p y ≪≫
    (lisseEtalePrimedFunctorHIsoGammaRightDerived f y p
      (lisseEtalePrimedPullback f y H)).symm

/-- The objectwise homology presheaf of `f'_* I` is the primed cohomology presheaf. -/
def lisseEtalePushforwardResolutionHomologyPresheafIso
    (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (homologyFunctor ((lisseEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (lisseEtalePushforwardResolutionPresheafComplex f H) ≅
      lisseEtaleHigherDirectImagePresheaf f H p :=
  NatIso.ofComponents
    (fun y ↦ lisseEtalePushforwardResolutionEvalHomologyIsoPrimedH f H p y.unop)
    sorry

/-- 103.15.2.1 (1): if `f : X ⟶ Y` is a smooth morphism of algebraic stacks and
`H` is an abelian sheaf on the lisse-étale site of `X`, then `R^p f'_* H` is
the sheaf associated to the presheaf sending a lisse-étale object `y` of `Y`,
lying over a scheme `V`, to `H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. Here
`(V ×_{y, Y} X)'` is `lisseEtalePrimedSite f y` and `pr'` is
`lisseEtalePrimedPr f y`. -/
@[stacks 07AW]
def lisseEtaleHigherDirectImageIso (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    lisseEtaleHigherDirectImage f H p ≅
      (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).obj
        (lisseEtaleHigherDirectImagePresheaf f H p) :=
  (injectiveResolution H).isoRightDerivedObj (lisseEtalePushforward f) p ≪≫
    lisseEtalePushforwardResolutionHomologySheafIso f H p ≪≫
    (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).mapIso
      (lisseEtalePushforwardResolutionHomologyPresheafIso f H p)

/-- The identification `R^p f'_* H ≅` sheafification of the primed cohomology presheaf is the
composite of the injective-resolution computation with sheafification of objectwise homology. -/
theorem lisseEtaleHigherDirectImageIso_spec (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    lisseEtaleHigherDirectImageIso f H p =
      (injectiveResolution H).isoRightDerivedObj (lisseEtalePushforward f) p ≪≫
        lisseEtalePushforwardResolutionHomologySheafIso f H p ≪≫
        (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).mapIso
          (lisseEtalePushforwardResolutionHomologyPresheafIso f H p) :=
  sorry

variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]

/-- Sheafification of abelian presheaves on the flat-fppf site of `Y` preserves homology. -/
instance flatFppfPresheafToSheaf_preservesHomology :
    (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).PreservesHomology :=
  sorry

/-- Continuous pullback to a primed flat-fppf fibre product is additive. -/
instance flatFppfPrimedPullbackFunctor.instAdditive
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    ((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfPrimedTopology f y) (flatFppfTopology X)).Additive :=
  sorry

/-- Continuous pullback to a primed flat-fppf fibre product preserves injective objects. -/
instance flatFppfPrimedPullbackFunctor.instPreservesInjectiveObjects
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    ((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfPrimedTopology f y) (flatFppfTopology X)).PreservesInjectiveObjects :=
  sorry

/-- Continuous pullback to a primed flat-fppf fibre product preserves homology. -/
instance flatFppfPrimedPullbackFunctor.instPreservesHomology
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    ((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfPrimedTopology f y) (flatFppfTopology X)).PreservesHomology :=
  sorry

/-- The abelian sheaf category on a primed flat-fppf fibre product has injective resolutions. -/
instance flatFppfPrimed_hasInjectiveResolutions
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    HasInjectiveResolutions
      (Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}) :=
  sorry

/-- The sheaf complex obtained by applying `f'_*` to a chosen injective resolution of `H`. -/
def flatFppfPushforwardResolutionComplex (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    HomologicalComplex (Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((flatFppfPushforward f).mapHomologicalComplex (up ℕ)).obj
    (injectiveResolution H).cocomplex

/-- The underlying presheaf complex of `flatFppfPushforwardResolutionComplex`. -/
def flatFppfPushforwardResolutionPresheafComplex (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    HomologicalComplex ((flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) :=
  ((sheafToPresheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (up ℕ)).obj (flatFppfPushforwardResolutionComplex f H)

/-- Sheafification of the underlying presheaf complex recovers the sheaf complex of `f'_* I`. -/
def flatFppfPushforwardResolutionComplexSheafifyIso (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    flatFppfPushforwardResolutionComplex f H ≅
      ((presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj (flatFppfPushforwardResolutionPresheafComplex f H) :=
  (Functor.mapHomologicalComplexIdIso
      (Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}) (up ℕ)).symm.app
      (flatFppfPushforwardResolutionComplex f H) ≪≫
    (NatIso.mapHomologicalComplex
        (sheafificationNatIso (flatFppfTopology Y) AddCommGrpCat.{u + 1})
        (up ℕ)).app (flatFppfPushforwardResolutionComplex f H) ≪≫
    (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (sheafToPresheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1} ⋙
            presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}))
        (up ℕ)).symm.app (flatFppfPushforwardResolutionComplex f H)

/-- Homology of `f'_* I` as a sheaf is the sheafification of the objectwise homology presheaf. -/
def flatFppfPushforwardResolutionHomologySheafIso (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (homologyFunctor (Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (flatFppfPushforwardResolutionComplex f H) ≅
      (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).obj
        ((homologyFunctor ((flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
          (flatFppfPushforwardResolutionPresheafComplex f H)) :=
  (homologyFunctor (Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}) (up ℕ) p).mapIso
      (flatFppfPushforwardResolutionComplexSheafifyIso f H) ≪≫
    (flatFppfPushforwardResolutionPresheafComplex f H).mapHomologyIso
      (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}) p

/-- The Hom functor corepresented by the constant integer sheaf on a primed flat-fppf site. -/
abbrev flatFppfPrimedHomFunctor (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))

/-- The primed flat-fppf Hom functor is additive. -/
instance flatFppfPrimedHomFunctor.instAdditive
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    (flatFppfPrimedHomFunctor f y).Additive :=
  inferInstance

/-- Morphisms from the constant integer sheaf compute global sections on a primed flat-fppf
fibre product. -/
def flatFppfPrimedHomIsoGamma (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    flatFppfPrimedHomFunctor f y ≅
      Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F ↦
      (Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
        (flatFppfPrimedTopology f y) F).toAddCommGrpIso.symm)
    sorry

/-- Homology of the corepresented Hom complex of an injective resolution is `Ext` from the
constant integer sheaf. -/
def flatFppfPrimedHomologyExtIso (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    {F : Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (p : ℕ) :
    (((flatFppfPrimedHomFunctor f y).mapHomologicalComplex (up ℤ)).obj
        I.cochainComplex).homology (Int.ofNat p) ≅
      AddCommGrpCat.of
        (Ext (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)) F p) :=
  HomologicalComplex.homologyMapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun i ↦
          (Cochain.fromSingleEquiv (zero_add i) :
              Cochain ((CochainComplex.singleFunctor _ 0).obj
                  (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))
                I.cochainComplex i ≃+
              (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y) ⟶
                I.cochainComplex.X i)).symm.toAddCommGrpIso)
        sorry)
      (Int.ofNat p) ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))
            I.cochainComplex (Int.ofNat p)).toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (homologyAddEquiv
            ((CochainComplex.singleFunctor _ 0).obj
              (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))
            I.cochainComplex (Int.ofNat p)).symm.toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry } ≪≫
    { hom :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)) F p ≃+
                CohomologyClass
                  ((CochainComplex.singleFunctor _ 0).obj
                    (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))
                  I.cochainComplex p).symm.toAddMonoidHom
      inv :=
        AddCommGrpCat.ofHom
          (I.extAddEquivCohomologyClass :
              Ext (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)) F p ≃+
                CohomologyClass
                  ((CochainComplex.singleFunctor _ 0).obj
                    (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)))
                  I.cochainComplex p).toAddMonoidHom
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Global cohomology on a primed flat-fppf fibre product is derived global sections. -/
def flatFppfPrimedFunctorHIsoGammaRightDerived (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) (p : ℕ)
    (F : Sheaf (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}) :
    (Sheaf.functorH (flatFppfPrimedTopology f y) p).obj F ≅
      ((Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).rightDerived p).obj F :=
  (Iso.refl ((Sheaf.functorH (flatFppfPrimedTopology f y) p).obj F) :
      (Sheaf.functorH (flatFppfPrimedTopology f y) p).obj F ≅
        AddCommGrpCat.of
          (Ext (constantIntegerSheaf.{u + 1, u, u + 1} (flatFppfPrimedTopology f y)) F p)) ≪≫
    (flatFppfPrimedHomologyExtIso f y (injectiveResolution F) p).symm ≪≫
    (InjectiveResolution.RightDerived.homologyIso
      (injectiveResolution F) (flatFppfPrimedHomFunctor f y) p) ≪≫
    (CategoryTheory.NatIso.rightDerived (flatFppfPrimedHomIsoGamma f y) p).app F

/-- Reindexing the Ran comma diagram along `costructuredArrowOpEquivalence` recovers the primed
projection. -/
def flatFppfPrimedLimitReindexIso (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (J : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    limit (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ J.obj) ≅
      limit ((flatFppfPrimedPr f y).op ⋙ J.obj) :=
  (HasLimit.isoOfEquivalence
      (costructuredArrowOpEquivalence (flatFppfMap f) y)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)).symm

/-- Underived evaluation of cocontinuous pushforward at `y` is global sections of the primed
pullback. -/
def flatFppfPushforwardEvalIsoGamma (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (J : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) :
    (((flatFppfPushforward f).obj J).obj.obj (op y)) ≅
      (Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).obj
        (flatFppfPrimedPullback f y J) :=
  ((flatFppfMap f).op.ranObjObjIsoLimit J.obj (op y)) ≪≫
    flatFppfPrimedLimitReindexIso f y J ≪≫
    (Sheaf.ΓNatIsoLim (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).symm.app
      (flatFppfPrimedPullback f y J)

/-- Degreewise underived comparison of the pushed injective resolution with global sections of
its primed pullback. -/
def flatFppfPushforwardResolutionEvalIsoGammaComplex (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (y : flatFppfSite Y) :
    (((evaluation (flatFppfSite Y)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)).mapHomologicalComplex
        (up ℕ)).obj (flatFppfPushforwardResolutionPresheafComplex f H) ≅
      ((Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (up ℕ)).obj
        ((((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (flatFppfPrimedTopology f y) (flatFppfTopology X)).mapHomologicalComplex
            (up ℕ)).obj (injectiveResolution H).cocomplex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      flatFppfPushforwardEvalIsoGamma f y ((injectiveResolution H).cocomplex.X n))
    sorry

/-- Objectwise homology of `f'_* I` at `y` is derived global sections of `(pr')⁻¹ H`. -/
def flatFppfPushforwardResolutionEvalHomologyIsoGammaRightDerived
    (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : flatFppfSite Y) :
    ((homologyFunctor ((flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (flatFppfPushforwardResolutionPresheafComplex f H)).obj (op y) ≅
      ((Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}).rightDerived p).obj
        (flatFppfPrimedPullback f y H) :=
  ((flatFppfPushforwardResolutionPresheafComplex f H).mapHomologyIso
        ((evaluation (flatFppfSite Y)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op y)) p).symm ≪≫
    (homologyFunctor AddCommGrpCat.{u + 1} (up ℕ) p).mapIso
      (flatFppfPushforwardResolutionEvalIsoGammaComplex f H y) ≪≫
    ((((flatFppfPrimedPr f y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (flatFppfPrimedTopology f y) (flatFppfTopology X)).mapInjectiveResolution
          (injectiveResolution H)).isoRightDerivedObj
        (Sheaf.Γ (flatFppfPrimedTopology f y) AddCommGrpCat.{u + 1}) p).symm

/-- Objectwise homology of `f'_* I` at `y` is global cohomology of `(pr')⁻¹ H`. -/
def flatFppfPushforwardResolutionEvalHomologyIsoPrimedH
    (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (y : flatFppfSite Y) :
    ((homologyFunctor ((flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (flatFppfPushforwardResolutionPresheafComplex f H)).obj (op y) ≅
      AddCommGrpCat.of ((flatFppfPrimedPullback f y H).H p) :=
  flatFppfPushforwardResolutionEvalHomologyIsoGammaRightDerived f H p y ≪≫
    (flatFppfPrimedFunctorHIsoGammaRightDerived f y p
      (flatFppfPrimedPullback f y H)).symm

/-- The objectwise homology presheaf of `f'_* I` is the primed cohomology presheaf. -/
def flatFppfPushforwardResolutionHomologyPresheafIso
    (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (homologyFunctor ((flatFppfSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (up ℕ) p).obj
        (flatFppfPushforwardResolutionPresheafComplex f H) ≅
      flatFppfHigherDirectImagePresheaf f H p :=
  NatIso.ofComponents
    (fun y ↦ flatFppfPushforwardResolutionEvalHomologyIsoPrimedH f H p y.unop)
    sorry

/-- 103.15.2.1 (2): if `f : X ⟶ Y` is a flat morphism of algebraic stacks and
`H` is an abelian sheaf on the flat-fppf site of `X`, then `R^p f'_* H` is the
sheaf associated to the presheaf sending a flat-fppf object `y` of `Y`, lying
over a scheme `V`, to `H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. Here
`(V ×_{y, Y} X)'` is `flatFppfPrimedSite f y` and `pr'` is
`flatFppfPrimedPr f y`. -/
@[stacks 07AW]
def flatFppfHigherDirectImageIso (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    flatFppfHigherDirectImage f H p ≅
      (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).obj
        (flatFppfHigherDirectImagePresheaf f H p) :=
  (injectiveResolution H).isoRightDerivedObj (flatFppfPushforward f) p ≪≫
    flatFppfPushforwardResolutionHomologySheafIso f H p ≪≫
    (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).mapIso
      (flatFppfPushforwardResolutionHomologyPresheafIso f H p)

/-- The identification `R^p f'_* H ≅` sheafification of the primed cohomology presheaf is the
composite of the injective-resolution computation with sheafification of objectwise homology. -/
theorem flatFppfHigherDirectImageIso_spec (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    flatFppfHigherDirectImageIso f H p =
      (injectiveResolution H).isoRightDerivedObj (flatFppfPushforward f) p ≪≫
        flatFppfPushforwardResolutionHomologySheafIso f H p ≪≫
        (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).mapIso
          (flatFppfPushforwardResolutionHomologyPresheafIso f H p) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
