/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import stacks_project.Chap96.Lemma_96_12_4
public import stacks_project.Chap103.Lemma_103_7_2
public import stacks_project.Chap103.Lemma_103_7_3
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import stacks_project.Chap103.Proposition_103_8_1_FppfSheaf
import StacksCheckRecall

/-!
# Locally quasi-coherent modules with the flat base change property

Summary of stability, sheaf, pullback, higher-direct-image, colimit, tensor,
and internal Hom properties of `LQCoh^{fbc}` on an algebraic stack.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty FiberedCategoryOver.Groupoids RingedSite.Hom
open scoped Bicategory

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Inverse image along `etaleFppfHom` exists, so étale modules may be
fppf-sheafified. -/
instance etaleFppfHom_modulePushforward_isRightAdjoint (X : GroupoidsOver S) :
    (etaleFppfHom X).modulePushforward.{u}.IsRightAdjoint := sorry

/-- Package an étale `LQCoh^{fbc}` module as an object of `Mod(𝒪_X)`, on the
same underlying module presheaf. -/
def toFppfModule_of_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    fppfModules X where
  val := etaleModulePresheaf F
  isSheaf := isSheaf_fppf_of_lqcohFbc F

/-- `toFppfModule_of_lqcohFbc F` has underlying module presheaf
`etaleModulePresheaf F`. -/
theorem toFppfModule_of_lqcohFbc_val {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    (toFppfModule_of_lqcohFbc F).val = etaleModulePresheaf F := rfl

/- Proposition 103.8.1 (2): `LQCoh^{fbc}(𝒪_X)` is a weak Serre subcategory of
`Mod(X_étale, 𝒪_X)`. -/
@[stacks 0771]
#check lqcohFbc_isWeakSerreClass

/- Proposition 103.8.1 (2): `LQCoh^{fbc}(𝒪_X)` is a weak Serre subcategory of
`Mod(𝒪_X)`. -/
@[stacks 0771]
#check FppfModules.lqcohFbc_isWeakSerreClass

namespace LQCohFbc

/-- Proposition 103.8.1 (3): pullback along a morphism of algebraic stacks
induces `f^* : LQCoh^{fbc}(𝒪_Y) ⥤ LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 0771]
def inverseImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : LQCohFbc Y ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (inclusion Y ⋙ moduleInverseImage f) (fun _ ↦ sorry)

/-- The underlying étale functor of `LQCohFbc.inverseImage f` is
`moduleInverseImage f`. -/
theorem inverseImage_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    inverseImage f ⋙ inclusion X = inclusion Y ⋙ moduleInverseImage f :=
  rfl

/-- Locally quasi-coherent étale modules with the flat base change property are
closed under colimits in `Mod(X_étale, 𝒪_X)`. -/
instance closedUnderColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] :
    (lqcohFbc X).IsClosedUnderColimitsOfShape J := sorry

/-- The inclusion `LQCoh^{fbc}(𝒪_X) ⥤ Mod(X_étale, 𝒪_X)` creates colimits of
every universe-compatible shape. -/
instance inclusion_createsColimitsOfShape (X : GroupoidsOver S)
    [AlgebraicStack X] (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] :
    CreatesColimitsOfShape J (inclusion X) :=
  createsColimitsOfShapeFullSubcategoryInclusion J (lqcohFbc X)

/-- Proposition 103.8.1 (5): the category `LQCoh^{fbc}(𝒪_X)` has colimits, and
they agree with colimits in `Mod(X_étale, 𝒪_X)`. -/
@[stacks 0771]
instance hasColimitsOfShape (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}] :
    HasColimitsOfShape J (LQCohFbc X) := sorry

/-- Colimits in `LQCoh^{fbc}(𝒪_X)` agree with colimits computed in
`Mod(X_étale, 𝒪_X)`. -/
def inclusion_colimitIso {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} [Category.{w} J] (F : J ⥤ LQCohFbc X)
    [HasColimit F] [HasColimit (F ⋙ inclusion X)]
    [PreservesColimit F (inclusion X)] :
    colimit (F ⋙ inclusion X) ≅ (inclusion X).obj (colimit F) :=
  (preservesColimitIso (inclusion X) F).symm

/-- `inclusion_colimitIso` is the inverse of the canonical
`preservesColimitIso`. -/
theorem inclusion_colimitIso_eq {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} [Category.{w} J] (F : J ⥤ LQCohFbc X)
    [HasColimit F] [HasColimit (F ⋙ inclusion X)]
    [PreservesColimit F (inclusion X)] :
    inclusion_colimitIso F = (preservesColimitIso (inclusion X) F).symm :=
  rfl

/-- The étale colimit of a diagram in `LQCoh^{fbc}` is already an fppf sheaf,
hence agrees with the colimit in `Mod(𝒪_X)`. -/
theorem colimit_isSheaf_fppf {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} [Category.{w} J] (F : J ⥤ LQCohFbc X) [HasColimit F] :
    Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf ((inclusion X).obj (colimit F))).presheaf :=
  sorry

/-- Proposition 103.8.1 (6): the tensor product of two objects of
`LQCoh^{fbc}(𝒪_X)`, computed in `Mod(X_étale, 𝒪_X)`, remains in
`LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 0771]
def tensor {X : GroupoidsOver S} [AlgebraicStack X] (F G : LQCohFbc X) :
    LQCohFbc X :=
  ⟨moduleTensorEtale F.obj G.obj, sorry⟩

/-- The underlying étale module of `LQCohFbc.tensor F G` is the étale tensor
product of the underlying modules. -/
theorem tensor_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : LQCohFbc X) :
    (tensor F G).obj = moduleTensorEtale F.obj G.obj := rfl

/-- Proposition 103.8.1 (7): sheaf Hom from a finitely presented étale
`𝒪_X`-module into an object of `LQCoh^{fbc}(𝒪_X)` remains in
`LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 0771]
def sheafHom {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X) :
    LQCohFbc X :=
  ⟨moduleSheafHomEtale F G.obj, sorry⟩

/-- The underlying étale module of `LQCohFbc.sheafHom F G` is
`moduleSheafHomEtale F G.obj`. -/
theorem sheafHom_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X) :
    (sheafHom F G).obj = moduleSheafHomEtale F G.obj := rfl

end LQCohFbc

/-- The total functor of a 1-morphism is continuous for associated fppf
ringed-site topologies. -/
instance toFunctor_fppfRinged_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).IsContinuous
      (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor f) (Scheme.fppfTopology.over S)

/-- The total functor of a 1-morphism is cocontinuous for associated fppf
ringed-site topologies. -/
instance toFunctor_fppfRinged_isCocontinuous {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).IsCocontinuous
      (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (Scheme.fppfTopology.over S)

/-- Type-valued sheafification exists on the associated fppf ringed site. -/
instance fppfRingedSite_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify (fppfRingedSite X).siteTopology (Type u) := sorry

/-- Ring-valued sheaves on the associated fppf topology compose with
`forget RingCat`. -/
instance fppfRingedSite_hasSheafCompose_forget_ring (X : GroupoidsOver S) :
    (fppfRingedSite X).siteTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of fppf structure sheaves. -/
def fppfStructureSheafIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology).obj
      (fppfRingedSite Y).structureSheaf ≅
      (fppfRingedSite X).structureSheaf :=
  (Functor.sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)
      (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- `fppfStructureSheafIso` is the continuous-pushforward comparison along
`comm f`. -/
theorem fppfStructureSheafIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfStructureSheafIso f =
      (Functor.sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) :=
  rfl

/-- The inverse-image form `f⁻¹ 𝒪_Y ⟶ 𝒪_X` as a map of underlying fppf
structure presheaves. -/
def fppfStructureSheafInversePresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (fppfRingedSite Y).structureSheaf.obj ⟶
      (fppfRingedSite X).structureSheaf.obj :=
  (Functor.sheafPushforwardContinuousCompSheafToPresheafIso (toFunctor f) RingCat.{u}
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology).inv.app
      (fppfRingedSite Y).structureSheaf ≫ (fppfStructureSheafIso f).hom.hom

/-- `fppfStructureSheafInversePresheaf` is the continuous identification
`f⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
theorem fppfStructureSheafInversePresheaf_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    fppfStructureSheafInversePresheaf f =
      (Functor.sheafPushforwardContinuousCompSheafToPresheafIso (toFunctor f) RingCat.{u}
            (fppfRingedSite X).siteTopology
            (fppfRingedSite Y).siteTopology).inv.app
          (fppfRingedSite Y).structureSheaf ≫
        (fppfStructureSheafIso f).hom.hom :=
  rfl

/-- The morphism of fppf ringed topoi induced by a 1-morphism, assembled so
that module pushforward lands in `fppfModules`. -/
def fppfModuleDirectImageToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (fppfRingedSite X) (fppfRingedSite Y) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
    (fppfRingedSite X) (fppfRingedSite Y) (toFunctor f)
    (toFunctor_fppfRinged_isCocontinuous f)
    (fppfRingedSite_hasSheafify_type X)
    (toFunctor_op_hasPointwiseRightKanExtension_type f)
    (fppfRingedSite_hasSheafCompose_forget_ring X)
    (fppfRingedSite_hasSheafCompose_forget_ring Y)
    (fppfStructureSheafInversePresheaf f)

/-- `fppfModuleDirectImageToposHom f` is the cocontinuous ringed-topos morphism
with structure map `fppfStructureSheafInversePresheaf f`. -/
theorem fppfModuleDirectImageToposHom_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModuleDirectImageToposHom f =
      @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
        (fppfRingedSite X) (fppfRingedSite Y) (toFunctor f)
        (toFunctor_fppfRinged_isCocontinuous f)
        (fppfRingedSite_hasSheafify_type X)
        (toFunctor_op_hasPointwiseRightKanExtension_type f)
        (fppfRingedSite_hasSheafCompose_forget_ring X)
        (fppfRingedSite_hasSheafCompose_forget_ring Y)
        (fppfStructureSheafInversePresheaf f) :=
  rfl

/-- Direct image `f_*` of fppf `𝒪`-modules along a 1-morphism, on
`GroupoidsOver.fppfModules`. -/
def fppfModuleDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModules X ⥤ fppfModules Y :=
  (fppfModuleDirectImageToposHom f).modulePushforward

/-- `fppfModuleDirectImage f` is module pushforward of
`fppfModuleDirectImageToposHom f`. -/
theorem fppfModuleDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModuleDirectImage f =
      (fppfModuleDirectImageToposHom f).modulePushforward :=
  rfl

/-- Fppf module direct image is additive. -/
instance fppfModuleDirectImage_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (fppfModuleDirectImage f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (fppfModuleDirectImageToposHom f)

/-- Fppf modules on a category fibred in groupoids admit injective
resolutions. -/
instance instHasInjectiveResolutions_fppfModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (fppfModules X) := sorry

/-- The degree-zero term of an existing injective resolution is an injective presentation. -/
private theorem enoughInjectives_of_resolutions {C : Type v} [Category.{w} C] [Abelian C]
    [HasInjectiveResolutions C] : EnoughInjectives C where
  presentation M := ⟨
    { J := (injectiveResolution M).cocomplex.X 0
      f := (injectiveResolution M).ι.f 0
      mono := mono_of_isLimit_fork (injectiveResolution M).isLimitKernelFork }⟩

/-- Existing fppf injective resolutions provide the presentations needed for bounded derivation. -/
instance fppfModules_enoughInjectives (X : GroupoidsOver S) :
    EnoughInjectives (fppfModules X) := enoughInjectives_of_resolutions

/-- Existing étale injective resolutions provide the presentations needed for bounded derivation. -/
instance etaleModules_enoughInjectives (X : GroupoidsOver S) :
    EnoughInjectives (etaleModules X) := enoughInjectives_of_resolutions

/-- The standard derived-category structure on fppf `𝒪_X`-modules. -/
instance fppfModules_hasDerivedCategory (X : GroupoidsOver S) :
    HasDerivedCategory (fppfModules X) :=
  HasDerivedCategory.standard (fppfModules X)

/-- The standard derived-category structure on étale `𝒪_X`-modules. -/
instance etaleModules_hasDerivedCategory (X : GroupoidsOver S) :
    HasDerivedCategory (etaleModules X) :=
  HasDerivedCategory.standard (etaleModules X)

/-- Restriction of fppf modules to étale modules is additive. -/
instance restriction_additive (X : GroupoidsOver S) :
    (restriction X).Additive := sorry

/-- Proposition 103.8.1 (4)(a): the higher direct image `R^i f_* F` may be
computed in the étale or the fppf topology with the same result. -/
@[stacks 0771]
theorem higherDirectImage_etale_iso_fppf {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F]
    (i : ℕ) :
    IsIsomorphic
      (((fppfModuleDirectImage f).rightDerived i).obj (toFppfModule_of_lqcohFbc F))
      (toFppfModule_of_lqcohFbc (moduleHigherDirectImage f F i)) :=
  sorry

/-- Proposition 103.8.1 (4)(a): the total direct image `Rf_* F` may be computed
in the étale or the fppf topology with the same result. -/
@[stacks 0771]
theorem derivedPushforward_etale_iso_fppf {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    IsIsomorphic
      (DerivedCategory.Plus.ι.obj
        ((restriction Y).rightDerivedFunctorPlus.obj
          ((fppfModuleDirectImage f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (fppfModules X) (0 : ℤ)).obj
              (toFppfModule_of_lqcohFbc F)))))
      (DerivedCategory.Plus.ι.obj
        ((moduleDirectImage f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (etaleModules X) (0 : ℤ)).obj F))) :=
  sorry

/-- Proposition 103.8.1 (4)(b): each étale higher direct image `R^i f_* F` of
an object of `LQCoh^{fbc}(𝒪_X)` along a quasi-compact quasi-separated morphism
of algebraic stacks lies in `LQCoh^{fbc}(𝒪_Y)`. -/
@[stacks 0771]
theorem mem_lqcohFbc_higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (F : etaleModules X)
    [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] (i : ℕ) :
    lqcohFbc Y (moduleHigherDirectImage f F i) := sorry

end AlgebraicGeometry.GroupoidsOver
