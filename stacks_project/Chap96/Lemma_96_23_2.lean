module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.«96_9_4_1_Comparison»
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap96.Lemma_96_23_1
public import stacks_project.Chap96.Lemma_96_23_2_Comparison

/-!
# Change of topology from fppf to étale for locally quasi-coherent modules

A locally quasi-coherent étale module on an algebraic stack, with 96.9.4.1
comparisons invertible along morphisms lying over flat locally finitely
presented scheme maps, is an fppf module. Derived pushforward along
`ε : X_fppf → X_étale` is ordinary pushforward, fppf and étale cohomology
agree, and higher direct images along a 1-morphism of CFGs are the
fppf-sheafifications of the étale ones.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits
open Functor.RightDerived
open FiberedCategoryOver.Groupoids
open scoped Bicategory

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageAb`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Hypothesis (b) of Lemma 96.23.2: the comparisons `c_φ` of 96.9.4.1 are
isomorphisms along morphisms of `X` lying over flat, locally of finite
presentation morphisms of schemes. -/
def HasFlatLfpModuleComparison {X : GroupoidsOver S} (F : etaleModules X) : Prop :=
  ∀ {x y : X.total} (φ : x ⟶ y),
    Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
      IsIso (moduleComparison φ F)

/-- `HasFlatLfpModuleComparison F` is the pointwise isomorphism condition on
`moduleComparison φ F` along flat locally finitely presented base maps. -/
theorem hasFlatLfpModuleComparison_iff {X : GroupoidsOver S} (F : etaleModules X) :
    HasFlatLfpModuleComparison F ↔
      ∀ {x y : X.total} (φ : x ⟶ y),
        Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
          IsIso (moduleComparison φ F) := sorry

/-- The single complex of a universe-lifted module sheaf, as an object of the
derived category. -/
abbrev singleDerivedModule (site : RingedSite.{u + 1, u, u})
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} site)]
    (M : RingedSite.ModuleCat.{u} site) :
    RingedSite.Hom.ModuleDerived.{u + 1} site :=
  (RingedSite.Hom.moduleLocalization.{u + 1} site).obj
    ((HomotopyCategory.singleFunctor
        (RingedSite.ModuleCat.{u + 1} site) 0).obj
      (RingedSite.Module.carrierLift site M))

/-- `singleDerivedModule` is localization of the degree-zero complex on the
carrier lift. -/
theorem singleDerivedModule_eq (site : RingedSite.{u + 1, u, u})
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} site)]
    (M : RingedSite.ModuleCat.{u} site) :
    singleDerivedModule site M =
      (RingedSite.Hom.moduleLocalization.{u + 1} site).obj
        ((HomotopyCategory.singleFunctor
            (RingedSite.ModuleCat.{u + 1} site) 0).obj
          (RingedSite.Module.carrierLift site M)) := sorry

/-- Abelian groups have sheafification on the fppf ringed site of `X`. -/
instance fppfRingedSite_hasSheafify_addCommGrpCat (X : GroupoidsOver S) :
    HasSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u} := sorry

/-- Abelian groups have sheafification on the associated étale site of `X`. -/
instance etaleTopology_hasSheafify_addCommGrpCat (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology AddCommGrpCat.{u} := sorry

/-- Ext groups exist for abelian sheaves on the fppf ringed site of `X`. -/
instance fppfRingedSite_hasExt_addCommGrpCat (X : GroupoidsOver S) :
    HasExt.{u} (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u}) := sorry

/-- Ext groups exist for abelian sheaves on the associated étale site of `X`. -/
instance etaleTopology_hasExt_addCommGrpCat (X : GroupoidsOver S) :
    HasExt.{u} (Sheaf X.etaleTopology AddCommGrpCat.{u}) := sorry

/-- Lifted abelian groups have weak sheafification on the fppf ringed site. -/
instance fppfRingedSite_hasWeakSheafify_addCommGrpCat_lift (X : GroupoidsOver S) :
    HasWeakSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Lifted abelian groups have weak sheafification on the associated étale
site. -/
instance etaleTopology_hasWeakSheafify_addCommGrpCat_lift (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{u + 1} := sorry

/-- The fppf ringed site of `X` has a global-sections functor on lifted
abelian groups. -/
instance fppfRingedSite_hasGlobalSectionsFunctor_lift (X : GroupoidsOver S) :
    HasGlobalSectionsFunctor (fppfRingedSite X).siteTopology
      AddCommGrpCat.{u + 1} := sorry

/-- The associated étale site of `X` has a global-sections functor on lifted
abelian groups. -/
instance etaleTopology_hasGlobalSectionsFunctor_lift (X : GroupoidsOver S) :
    HasGlobalSectionsFunctor X.etaleTopology AddCommGrpCat.{u + 1} := sorry

/-- Lifted fppf modules on `X` form a Grothendieck abelian category. -/
instance fppfModules_isGrothendieckAbelian_lift (X : GroupoidsOver S) :
    IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (fppfRingedSite X)) :=
  sorry

/-- Lifted étale modules on `X` form a Grothendieck abelian category. -/
instance etaleModules_isGrothendieckAbelian_lift (X : GroupoidsOver S) :
    IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (etaleRingedSite X)) :=
  sorry

/-- Cocontinuous abelian pushforward of a 1-morphism on a pair of inherited
topologies. -/
abbrev abelianPushforwardAlong {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (J : GrothendieckTopology X.total) (K : GrothendieckTopology Y.total)
    [(toCartesianBasedFunctor f).toFunctor.IsCocontinuous J K]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
    AddCommGrpCat.{u} J K

/-- `abelianPushforwardAlong` is cocontinuous sheaf pushforward of the
cartesian total functor. -/
theorem abelianPushforwardAlong_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (J : GrothendieckTopology X.total) (K : GrothendieckTopology Y.total)
    [(toCartesianBasedFunctor f).toFunctor.IsCocontinuous J K]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    abelianPushforwardAlong f J K =
      (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
        AddCommGrpCat.{u} J K := sorry

/-- The cartesian total functor is cocontinuous for the fppf ringed sites. -/
instance toCartesianBasedFunctor_isCocontinuous_fppfRinged
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toCartesianBasedFunctor f).toFunctor.IsCocontinuous
      (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  sorry

/-- The cartesian total functor is cocontinuous for the associated étale
topologies. -/
instance toCartesianBasedFunctor_isCocontinuous_etale
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toCartesianBasedFunctor f).toFunctor.IsCocontinuous
      X.etaleTopology Y.etaleTopology := sorry

/-- Pointwise right Kan extensions along the opposite cartesian total functor
exist on abelian presheaves. -/
instance toCartesianBasedFunctor_op_hasPointwiseRightKanExtension_addCommGrpCat
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- Abelian sheaves on the fppf ringed site of `X` form an abelian category. -/
instance fppfRingedSite_sheaf_abelian (X : GroupoidsOver S) :
    Abelian (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u}) :=
  inferInstance

/-- Abelian sheaves on the associated étale site of `X` form an abelian
category. -/
instance etaleTopology_sheaf_abelian (X : GroupoidsOver S) :
    Abelian (Sheaf X.etaleTopology AddCommGrpCat.{u}) := inferInstance

/-- Abelian sheaves on the fppf ringed site of `X` admit injective
resolutions. -/
instance fppfRingedSite_sheaf_hasInjectiveResolutions (X : GroupoidsOver S) :
    HasInjectiveResolutions
      (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u}) := sorry

/-- Abelian sheaves on the associated étale site of `X` admit injective
resolutions. -/
instance etaleTopology_sheaf_hasInjectiveResolutions (X : GroupoidsOver S) :
    HasInjectiveResolutions (Sheaf X.etaleTopology AddCommGrpCat.{u}) :=
  sorry

/-- Cocontinuous abelian pushforward on fppf ringed sites is additive. -/
instance abelianPushforwardAlong_fppf_additive {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (abelianPushforwardAlong f (fppfRingedSite X).siteTopology
      (fppfRingedSite Y).siteTopology).Additive := sorry

/-- Cocontinuous abelian pushforward on associated étale sites is additive. -/
instance abelianPushforwardAlong_etale_additive {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (abelianPushforwardAlong f X.etaleTopology Y.etaleTopology).Additive :=
  sorry

/-- Degree-`i` higher direct image of an abelian sheaf along a 1-morphism. -/
noncomputable def higherDirectImageAb {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (J : GrothendieckTopology X.total) (K : GrothendieckTopology Y.total)
    [(toCartesianBasedFunctor f).toFunctor.IsCocontinuous J K]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    [Abelian (Sheaf J AddCommGrpCat.{u})]
    [Abelian (Sheaf K AddCommGrpCat.{u})]
    [(abelianPushforwardAlong f J K).Additive]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u}) (i : ℕ) :
    Sheaf K AddCommGrpCat.{u} :=
  ((abelianPushforwardAlong f J K).rightDerived i).obj G

/-- `higherDirectImageAb` is the object map of `rightDerived` of
`abelianPushforwardAlong`. -/
theorem higherDirectImageAb_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (J : GrothendieckTopology X.total) (K : GrothendieckTopology Y.total)
    [(toCartesianBasedFunctor f).toFunctor.IsCocontinuous J K]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    [Abelian (Sheaf J AddCommGrpCat.{u})]
    [Abelian (Sheaf K AddCommGrpCat.{u})]
    [(abelianPushforwardAlong f J K).Additive]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u}) (i : ℕ) :
    higherDirectImageAb f J K G i =
      ((abelianPushforwardAlong f J K).rightDerived i).obj G := sorry

variable {X : GroupoidsOver S} [AlgebraicStack X]
variable (F : etaleModules X) [IsLocallyQuasiCoherent F]
variable (h_comparison : HasFlatLfpModuleComparison F)
include h_comparison

/-- Lemma 96.23.2 (1): if `X` is an algebraic stack over `S` and `F` is a
locally quasi-coherent étale `𝒪_X`-module such that `moduleComparison φ F` is
an isomorphism whenever `φ` lies over a flat and locally of finite
presentation morphism of schemes, then `F` is an `𝒪_X`-module on the fppf
site. -/
@[stacks 075R]
theorem isSheaf_fppf :
    Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf F).presheaf :=
  sorry

/-- Lemma 96.23.2 (2): with the same hypotheses, `Rε_* F = ε_* F` along the
identity comparison `ε : X_fppf → X_étale`. -/
@[stacks 075R]
theorem rightDerived_eq_pushforward
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u} (fppfRingedSite X))] :
    Vanishes.aboveZero (etaleFppfHom X).modulePushforward.{u}
      (toFppfModule F (isSheaf_fppf F h_comparison)) :=
  sorry

/-- Positive higher direct images of `toFppfModule F` along `etaleFppfHom`
vanish. -/
theorem rightDerived_eq_pushforward_vanishesAboveZero_iff
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u} (fppfRingedSite X))] :
    Vanishes.aboveZero (etaleFppfHom X).modulePushforward.{u}
      (toFppfModule F (isSheaf_fppf F h_comparison)) ↔
      ∀ q : ℕ, 0 < q →
        IsZero
          (((etaleFppfHom X).modulePushforward.{u}.rightDerived q).obj
            (toFppfModule F (isSheaf_fppf F h_comparison))) :=
  sorry

/-- Lemma 96.23.2 (3): fppf and étale cohomology groups `H^p(X, F)` agree. -/
@[stacks 075R]
theorem cohomology_fppf_isomorphic_etale (p : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH (fppfRingedSite X).siteTopology p).obj
        (fppfAbelianSheaf F (isSheaf_fppf F h_comparison)))
      ((Sheaf.functorH X.etaleTopology p).obj (etaleAbelianSheaf F)) :=
  sorry

/-- Lemma 96.23.2 (4): objectwise cohomology groups `H^p(x, F)` agree in the
fppf and étale topologies. -/
@[stacks 075R]
theorem cohomology_objectwise_fppf_isomorphic_etale (p : ℕ) (x : X.total) :
    IsIsomorphic
      ((fppfAbelianSheaf F (isSheaf_fppf F h_comparison)).H' p x)
      ((etaleAbelianSheaf F).H' p x) :=
  sorry

/-- Lemma 96.23.2 (5): derived global sections `RΓ(X, F)` agree in the fppf
and étale topologies. -/
@[stacks 075R]
theorem derivedGlobalSections_fppf_isomorphic_etale :
    IsIsomorphic
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1}
          (fppfRingedSite X)).obj
        (singleDerivedModule (fppfRingedSite X) (toFppfModule F (isSheaf_fppf F h_comparison))))
      ((RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1}
          (etaleRingedSite X)).obj
        (singleDerivedModule (etaleRingedSite X) F)) :=
  sorry

/-- Lemma 96.23.2 (6): objectwise derived sections `RΓ(x, F)` agree in the
fppf and étale topologies. -/
@[stacks 075R]
theorem derivedSections_objectwise_fppf_isomorphic_etale (x : X.total) :
    IsIsomorphic
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (fppfRingedSite X) x).obj
        (singleDerivedModule (fppfRingedSite X) (toFppfModule F (isSheaf_fppf F h_comparison))))
      ((RingedSite.Hom.moduleSectionsDerived.{u + 1} (etaleRingedSite X) x).obj
        (singleDerivedModule (etaleRingedSite X) F)) :=
  sorry

/-- Lemma 96.23.2 (7): if `f : X ⟶ Y` is a 1-morphism of categories fibred in
groupoids, then `R^i f_* F` in the fppf topology is the fppf-sheafification of
the étale higher direct image. -/
@[stacks 075R]
theorem higherDirectImage_fppf_iso_sheafify_etale {Y : GroupoidsOver S}
    (f : X ⟶ Y) (i : ℕ)
    [HasWeakSheafify (fppfRingedSite Y).siteTopology AddCommGrpCat.{u}]
    [∀ P : Y.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (𝟭 Y.total).op.HasLeftKanExtension P] :
    IsIsomorphic
      (higherDirectImageAb f (fppfRingedSite X).siteTopology
        (fppfRingedSite Y).siteTopology
        (fppfAbelianSheaf F (isSheaf_fppf F h_comparison)) i)
      ((GrothendieckTopology.TopologyComparison.pullback AddCommGrpCat.{u}
          (etaleRingedSite_le_fppfRingedSite Y)).obj
        (higherDirectImageAb f X.etaleTopology Y.etaleTopology
          (etaleAbelianSheaf F) i)) :=
  sorry

/-- Lemma 96.23.2 (8): derived pullback of `F` along a 1-morphism `g : Z ⟶ X`
agrees, after fppf-sheafification, with the étale module inverse image. -/
@[stacks 075R]
theorem derivedPullback_fppf_iso_sheafify_etale {Z : GroupoidsOver S}
    (g : Z ⟶ X)
    [(etaleFppfHom Z).modulePushforward.{u}.IsRightAdjoint] :
    IsIsomorphic
      ((modulePullback g).obj
        (toFppfModule F (isSheaf_fppf F h_comparison)))
      ((RingedSite.Hom.modulePullback.{u} (etaleFppfHom Z)).obj
        ((moduleInverseImage g).obj F)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
