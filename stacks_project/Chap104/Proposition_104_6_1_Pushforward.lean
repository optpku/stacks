/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage
public import stacks_project.Chap104.«104_5_1_1_Homology»
public import stacks_project.Chap104.Proposition_104_6_1_Plus

/-!
# Bounded-below derived pushforward of quasi-coherent modules

A quasi-compact quasi-separated morphism of algebraic stacks has a derived
direct image `Rf_*` which preserves `D⁺_{Parasitic ∩ LQCoh^{fbc}}` and
`D⁺_{LQCoh^{fbc}}`. Restricting the unbounded `moduleDerivedPushforward` and
factoring through the parasitic Verdier quotient produces
`Rf_{QCoh,*} : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(𝒪_Y)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace FppfDerivedPushforwardImpl

/-- Type-valued sheafification exists on the associated fppf site. -/
instance fppfTopology_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify (fppfRingedSite X).siteTopology (Type u) := sorry

/-- Ring-valued sheaves on the associated fppf topology compose with the
forgetful functor to types. -/
instance fppfTopology_hasSheafCompose_ring (X : GroupoidsOver S) :
    (fppfRingedSite X).siteTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The projection of a category fibred in groupoids is continuous for the
inherited fppf topology. -/
instance p_isContinuous_fppf (X : GroupoidsOver S) :
    X.p.IsContinuous (inheritedFppfTopology X) (Scheme.fppfTopology.over S) :=
  sorry

/-- The total functor of a 1-morphism is continuous for associated fppf
topologies. -/
instance toFunctor_isContinuous_fppf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).IsContinuous
      (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  sorry

/-- The total functor of a 1-morphism is cocontinuous for associated fppf
topologies. -/
instance toFunctor_isCocontinuous_fppf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).IsCocontinuous
      (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued presheaves along the
opposite of a 1-morphism of fppf sites. -/
instance toFunctor_op_hasPointwiseRightKanExtension_type_fppf
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (P : (fppfRingedSite X)ᵒᵖ ⥤ Type u) :
    (toFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of fppf structure sheaves. -/
def fppfStructureSheafIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology).obj
      (fppfRingedSite Y).structureSheaf ≅
      (fppfRingedSite X).structureSheaf :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)
      (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- `fppfStructureSheafIso` is the continuous-pushforward comparison along
`comm f`. -/
theorem fppfStructureSheafIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfStructureSheafIso f =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) := sorry

/-- Fppf modules on a category fibred in groupoids form a Grothendieck abelian
category. -/
instance fppfModules_isGrothendieckAbelian (X : GroupoidsOver S) :
    IsGrothendieckAbelian.{u + 1} (fppfModules X) := sorry

end FppfDerivedPushforwardImpl

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidsOver
open GroupoidsOver.FppfDerivedPushforwardImpl

variable {S : Scheme.{u}}

namespace FppfDerivedPushforwardImpl

/-- The inverse-image form `f⁻¹ 𝒪_Y ⟶ 𝒪_X` as a map of underlying structure
presheaves. -/
def fppfStructureSheafInversePresheaf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (fppfRingedSite Y).structureSheaf.obj ⟶
      (fppfRingedSite X).structureSheaf.obj :=
  (sheafPushforwardContinuousCompSheafToPresheafIso (toFunctor f) RingCat.{u}
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology).inv.app
      (fppfRingedSite Y).structureSheaf ≫
    (fppfStructureSheafIso f).hom.hom

/-- The inverse-image structure-sheaf map as a presheaf morphism is the
continuous identification `f⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
theorem fppfStructureSheafInversePresheaf_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    fppfStructureSheafInversePresheaf f =
      (sheafPushforwardContinuousCompSheafToPresheafIso (toFunctor f) RingCat.{u}
            (fppfRingedSite X).siteTopology
            (fppfRingedSite Y).siteTopology).inv.app
          (fppfRingedSite Y).structureSheaf ≫
        (fppfStructureSheafIso f).hom.hom := sorry

/-- The morphism of fppf ringed topoi induced by a 1-morphism of categories
fibred in groupoids. -/
def fppfRingedToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (fppfRingedSite X) (fppfRingedSite Y) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (fppfRingedSite X) (fppfRingedSite Y) (toFunctor f) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (fppfStructureSheafInversePresheaf f)

/-- Underived module direct image along a 1-morphism of algebraic stacks,
as fppf `𝒪`-modules. -/
def modulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModules X ⥤ fppfModules Y :=
  (fppfRingedToposHom f).modulePushforward

/-- `modulePushforward` is module direct image along `fppfRingedToposHom`. -/
theorem modulePushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    modulePushforward f =
      RingedSite.ToposHom.modulePushforward (fppfRingedToposHom f) := sorry

/-- Module direct image along `fppfRingedToposHom` is additive. -/
instance modulePushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (modulePushforward f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (fppfRingedToposHom f)

/-- Fppf modules admit injective resolutions. -/
instance fppfModules_hasInjectiveResolutions (X : GroupoidsOver S) :
    HasInjectiveResolutions (fppfModules X) := sorry

/-- Bounded-below module pushforward admits a total right derived functor. -/
instance modulePushforward_toBoundedBelowDerived_hasRightDerived
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    (modulePushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (fppfModules X)) := sorry

/-- Unbounded derived pushforward `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of fppf modules
along a 1-morphism of algebraic stacks. This is the Chap110 owner, reconstructed
here because `Lemma_110_61_3_Pushforward` cannot be imported together with
`Proposition_103_11_1_DirectImage`. -/
noncomputable abbrev moduleDerivedPushforward {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.RightDerived.KInjective.functor (modulePushforward f)

/-- `moduleDerivedPushforward` is the K-injective total right derived functor of
`modulePushforward`. -/
theorem moduleDerivedPushforward_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    moduleDerivedPushforward f =
      Functor.RightDerived.KInjective.functor (modulePushforward f) := sorry

/-- Homotopy-to-derived module pushforward has a pointwise right derived
functor at quasi-isomorphisms. -/
instance homotopyToDerived_modulePushforward_hasPointwiseRightDerived
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (Homotopy.toDerived (modulePushforward f)).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (fppfModules X) (ComplexShape.up ℤ)) := sorry

/-- Unbounded `Rf_*` commutes with shifts. -/
instance moduleDerivedPushforward.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (moduleDerivedPushforward f).CommShift ℤ :=
  totalRightDerived_commShift
    (Homotopy.toDerived (modulePushforward f))
    (HomotopyCategory.quasiIso (fppfModules X) (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (fppfModules X) (ComplexShape.up ℤ) ⥤
        DerivedCategory (fppfModules X))

/-- Unbounded `Rf_*` is triangulated. -/
instance moduleDerivedPushforward.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (moduleDerivedPushforward f).IsTriangulated := sorry

end FppfDerivedPushforwardImpl

/-- Unbounded derived pushforward `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of fppf modules.
This is a local reconstruction of the Chap110 owner, uniquely named so this
module can be imported with `Proposition_103_11_1_DirectImage`. -/
def fppfModuleDerivedPushforward {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  FppfDerivedPushforwardImpl.moduleDerivedPushforward f

/-- Unbounded `Rf_*` sends bounded-below objects to bounded-below objects. -/
theorem fppfModuleDerivedPushforward_mem_plus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {E : ModuleDerived X}
    (h : (t.plus : ObjectProperty (ModuleDerived X)) E) :
    (t.plus : ObjectProperty (ModuleDerived Y))
      ((fppfModuleDerivedPushforward f).obj E) := sorry

/-- Unbounded `Rf_*` commutes with shifts. -/
instance fppfModuleDerivedPushforward.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (fppfModuleDerivedPushforward f).CommShift ℤ :=
  FppfDerivedPushforwardImpl.moduleDerivedPushforward.instCommShift f

/-- Unbounded `Rf_*` is triangulated. -/
instance fppfModuleDerivedPushforward.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (fppfModuleDerivedPushforward f).IsTriangulated := sorry

end AlgebraicGeometry.AlgebraicStack


namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Unbounded derived pushforward preserves bounded-below objects. -/
theorem mapsTo_plus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (t.plus : ObjectProperty (ModuleDerived X)) ≤
      (t.plus : ObjectProperty (ModuleDerived Y)).inverseImage
        (fppfModuleDerivedPushforward f) := sorry

/-- Bounded-below restriction of unbounded `Rf_*`. -/
def moduleDerivedPushforwardPlus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Plus (fppfModules X) ⥤ Plus (fppfModules Y) :=
  FullSubcategory.restrict (fppfModuleDerivedPushforward f) (mapsTo_plus f)

/-- `moduleDerivedPushforwardPlus` is the restriction of unbounded
`moduleDerivedPushforward`. -/
theorem moduleDerivedPushforwardPlus_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    moduleDerivedPushforwardPlus f =
      FullSubcategory.restrict (fppfModuleDerivedPushforward f) (mapsTo_plus f) :=
  sorry

/-- Inclusion comparison for the bounded-below restriction of `Rf_*`. -/
def moduleDerivedPushforwardPlus_comp_ι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    moduleDerivedPushforwardPlus f ⋙ Plus.ι ≅
      Plus.ι ⋙ fppfModuleDerivedPushforward f :=
  FullSubcategory.restrict.compιIso (fppfModuleDerivedPushforward f) (mapsTo_plus f)

/-- The inclusion comparison is the canonical restriction comparison. -/
theorem moduleDerivedPushforwardPlus_comp_ι_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    moduleDerivedPushforwardPlus_comp_ι f =
      FullSubcategory.restrict.compιIso (fppfModuleDerivedPushforward f)
        (mapsTo_plus f) := sorry

/-- Bounded-below `Rf_*` commutes with shifts. -/
instance moduleDerivedPushforwardPlus.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (moduleDerivedPushforwardPlus f).CommShift ℤ :=
  Functor.CommShift.ofComp (moduleDerivedPushforwardPlus_comp_ι f) ℤ

/-- Bounded-below `Rf_*` is triangulated. -/
instance moduleDerivedPushforwardPlus.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (moduleDerivedPushforwardPlus f).IsTriangulated := sorry

/-- Bounded-below `Rf_*` preserves `D⁺_{LQCoh^{fbc}}`. -/
theorem mapsTo_plus_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Plus.cohomologyIn (FppfModules.lqcohFbc X) ≤
      (Plus.cohomologyIn (FppfModules.lqcohFbc Y)).inverseImage
        (moduleDerivedPushforwardPlus f) := sorry

/-- Middle vertical arrow: `Rf_*` on `D⁺_{LQCoh^{fbc}}`. -/
def derivedPushforwardPlusLQCohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedLQCohFbc.Plus X ⥤ DerivedLQCohFbc.Plus Y :=
  FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_lqcohFbc f)

/-- `derivedPushforwardPlusLQCohFbc` is the restriction of
`moduleDerivedPushforwardPlus` to `D⁺_{LQCoh^{fbc}}`. -/
theorem derivedPushforwardPlusLQCohFbc_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc f =
      FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
        (mapsTo_plus_lqcohFbc f) := sorry

/-- Right commuting square: restriction to `D⁺_{LQCoh^{fbc}}` whiskers with
the inclusions into `D⁺(𝒪)`. -/
def derivedPushforwardPlusLQCohFbc_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.inclusion Y ≅
      DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f :=
  FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_lqcohFbc f)

/-- The plus-level inclusion comparison is the canonical restriction
comparison. -/
theorem derivedPushforwardPlusLQCohFbc_comp_inclusion_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc_comp_inclusion f =
      FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
        (mapsTo_plus_lqcohFbc f) := sorry

/-- Right square of the source diagram: `Rf_*` on `D⁺_{LQCoh^{fbc}}` whiskers
with the ambient inclusions into unbounded `D(𝒪)`. -/
def derivedPushforwardPlusLQCohFbc_comp_ambient {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ≅
      DerivedLQCohFbc.Plus.ambient X ⋙ fppfModuleDerivedPushforward f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedPushforwardPlusLQCohFbc_comp_inclusion f)
      Plus.ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedLQCohFbc.Plus.inclusion X)
      (moduleDerivedPushforwardPlus_comp_ι f)

/-- The ambient comparison is the composite of the plus-level restriction
comparison with `moduleDerivedPushforwardPlus_comp_ι`. -/
theorem derivedPushforwardPlusLQCohFbc_comp_ambient_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusLQCohFbc_comp_ambient f =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (derivedPushforwardPlusLQCohFbc_comp_inclusion f) Plus.ι ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (DerivedLQCohFbc.Plus.inclusion X)
          (moduleDerivedPushforwardPlus_comp_ι f) := sorry

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` commutes with shifts. -/
instance derivedPushforwardPlusLQCohFbc.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusLQCohFbc f).CommShift ℤ :=
  Functor.CommShift.ofComp
    (derivedPushforwardPlusLQCohFbc_comp_inclusion f) ℤ

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` is triangulated. -/
instance derivedPushforwardPlusLQCohFbc.instIsTriangulated
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusLQCohFbc f).IsTriangulated := sorry

/-- Bounded-below `Rf_*` preserves `D⁺_{Parasitic ∩ LQCoh^{fbc}}`. -/
theorem mapsTo_plus_parasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X) ≤
      (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc Y)).inverseImage
        (moduleDerivedPushforwardPlus f) := sorry

/-- Left vertical arrow: `Rf_*` on `D⁺_{Parasitic ∩ LQCoh^{fbc}}`. -/
def derivedPushforwardPlusParasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedParasiticLQCohFbcPlus X ⥤ derivedParasiticLQCohFbcPlus Y :=
  FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_parasitic f)

/-- `derivedPushforwardPlusParasitic` is the restriction of
`moduleDerivedPushforwardPlus` to parasitic plus objects. -/
theorem derivedPushforwardPlusParasitic_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic f =
      FullSubcategory.restrict (moduleDerivedPushforwardPlus f)
        (mapsTo_plus_parasitic f) := sorry

/-- Left commuting square: restriction to parasitic plus objects whiskers with
the inclusions into `D⁺(𝒪)`. -/
def derivedPushforwardPlusParasitic_comp_ι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic f ⋙
        (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc Y)).ι ≅
      (Plus.cohomologyIn (FppfModules.parasiticLQCohFbc X)).ι ⋙
        moduleDerivedPushforwardPlus f :=
  FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
    (mapsTo_plus_parasitic f)

/-- The parasitic plus inclusion comparison is the canonical restriction
comparison. -/
theorem derivedPushforwardPlusParasitic_comp_ι_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic_comp_ι f =
      FullSubcategory.restrict.compιIso (moduleDerivedPushforwardPlus f)
        (mapsTo_plus_parasitic f) := sorry

/-- Left square of the source diagram: `Rf_*` on parasitic plus objects
whiskers with the inclusions into `D⁺_{LQCoh^{fbc}}`. -/
def derivedPushforwardPlusParasitic_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedPushforwardPlusParasitic f ⋙
        derivedParasiticLQCohFbcPlus.inclusion Y ≅
      derivedParasiticLQCohFbcPlus.inclusion X ⋙
        derivedPushforwardPlusLQCohFbc f :=
  ((Plus.cohomologyIn (FppfModules.lqcohFbc Y)).fullyFaithfulι.whiskeringRight
      (derivedParasiticLQCohFbcPlus X)).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedPushforwardPlusParasitic f)
        (Plus.CohomologyIn.inclusion.compιIso
          (FppfModules.parasiticLQCohFbc_le_lqcohFbc Y)) ≪≫
      derivedPushforwardPlusParasitic_comp_ι f ≪≫
      Functor.isoWhiskerRight
        (Plus.CohomologyIn.inclusion.compιIso
          (FppfModules.parasiticLQCohFbc_le_lqcohFbc X)).symm
        (moduleDerivedPushforwardPlus f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedParasiticLQCohFbcPlus.inclusion X)
        (derivedPushforwardPlusLQCohFbc_comp_inclusion f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The parasitic inclusion comparison is inverted by its inverse. -/
theorem derivedPushforwardPlusParasitic_comp_inclusion_hom_inv_id
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusParasitic_comp_inclusion f).hom ≫
      (derivedPushforwardPlusParasitic_comp_inclusion f).inv = 𝟙 _ := sorry

/-- Restricted `Rf_*` on parasitic plus objects commutes with shifts. -/
instance derivedPushforwardPlusParasitic.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusParasitic f).CommShift ℤ :=
  Functor.CommShift.ofComp (derivedPushforwardPlusParasitic_comp_ι f) ℤ

/-- Restricted `Rf_*` on parasitic plus objects is triangulated. -/
instance derivedPushforwardPlusParasitic.instIsTriangulated
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedPushforwardPlusParasitic f).IsTriangulated := sorry

/-- Restricted `Rf_*` on `D⁺_{LQCoh^{fbc}}` sends parasitic plus objects to
parasitic plus objects. -/
theorem derivedPushforwardPlusLQCohFbc_maps_parasitic {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    derivedParasiticPlus X ≤
      (derivedParasiticPlus Y).inverseImage
        (derivedPushforwardPlusLQCohFbc f) := sorry

namespace DerivedQCoh

/-- Composite of plus `Rf_*` on `LQCoh^{fbc}` with the plus Verdier quotient
functor on the target. -/
def pushforwardToPlus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedLQCohFbc.Plus X ⥤ DerivedQCoh.Plus Y :=
  derivedPushforwardPlusLQCohFbc f ⋙ DerivedQCoh.Plus.quotientFunctor Y

/-- `pushforwardToPlus` is plus `Rf_*` followed by the target plus quotient
functor. -/
theorem pushforwardToPlus_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    pushforwardToPlus f =
      derivedPushforwardPlusLQCohFbc f ⋙
        DerivedQCoh.Plus.quotientFunctor Y := sorry

/-- The composite through `D⁺_QCoh(𝒪_Y)` inverts the plus parasitic Verdier
system. -/
theorem pushforwardToPlus_inverts {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (derivedParasiticPlus X).trW.IsInvertedBy (pushforwardToPlus f) := sorry

/-- `pushforwardToPlus` commutes with shifts. -/
instance pushforwardToPlus.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforwardToPlus f).CommShift ℤ :=
  inferInstanceAs
    ((derivedPushforwardPlusLQCohFbc f ⋙
        DerivedQCoh.Plus.quotientFunctor Y).CommShift ℤ)

/-- `pushforwardToPlus` is triangulated. -/
instance pushforwardToPlus.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforwardToPlus f).IsTriangulated := sorry

/-- Derived quasi-coherent pushforward
`Rf_{QCoh,*} : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(𝒪_Y)`. -/
def pushforward {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus Y :=
  VerdierQuotient.Exact.factor (derivedParasiticPlus X)
    (pushforwardToPlus f) (pushforwardToPlus_inverts f)

/-- `pushforward` is the exact Verdier factor of `pushforwardToPlus`. -/
theorem pushforward_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    pushforward f =
      VerdierQuotient.Exact.factor (derivedParasiticPlus X)
        (pushforwardToPlus f) (pushforwardToPlus_inverts f) := sorry

/-- Canonical comparison from the plus quotient functor followed by
`pushforward` to `pushforwardToPlus`. -/
def pushforward_facIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus.quotientFunctor X ⋙ pushforward f ≅
      pushforwardToPlus f :=
  VerdierQuotient.Exact.factor.facIso (derivedParasiticPlus X)
    (pushforwardToPlus f) (pushforwardToPlus_inverts f)

/-- Strict factorization of `pushforward` through the plus quotient functor. -/
theorem pushforward_fac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    DerivedQCoh.Plus.quotientFunctor X ⋙ pushforward f =
      pushforwardToPlus f := sorry

/-- `Rf_{QCoh,*}` commutes with shifts. -/
instance pushforward.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforward f).CommShift ℤ :=
  VerdierQuotient.Exact.factor.commShift (derivedParasiticPlus X)
    (pushforwardToPlus f) (pushforwardToPlus_inverts f)

/-- `Rf_{QCoh,*}` is triangulated. -/
instance pushforward.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (pushforward f).IsTriangulated :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasiticPlus X)
    (pushforwardToPlus f) (pushforwardToPlus_inverts f)

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver.QCoh

open AlgebraicGeometry.AlgebraicStack DerivedCategory

variable {S : Scheme.{u}}

/-- Quasi-coherent fppf modules lie in fppf `LQCoh^{fbc}`. -/
theorem mem_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X] (F : QCoh X) :
    FppfModules.lqcohFbc X ((QCoh.inclusion X).obj F) := sorry

/-- The inclusion of quasi-coherent modules into fppf `LQCoh^{fbc}`. -/
def toFppfLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ FppfModules.LQCohFbc X :=
  (FppfModules.lqcohFbc X).lift (QCoh.inclusion X) mem_lqcohFbc

/-- The underlying fppf module of `toFppfLQCohFbc` is `QCoh.inclusion`. -/
theorem toFppfLQCohFbc_comp_inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] :
    toFppfLQCohFbc X ⋙ FppfModules.inclusion X = QCoh.inclusion X :=
  rfl

/-- The Serre quotient of fppf `LQCoh^{fbc}` applied to a quasi-coherent
module. -/
def toFppfQuotient (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ FppfModules.LQCohFbc.Quotient X :=
  toFppfLQCohFbc X ⋙ FppfModules.LQCohFbc.toQCoh X

/-- `toFppfQuotient` is `toFppfLQCohFbc` followed by `toQCoh`. -/
theorem toFppfQuotient_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    toFppfQuotient X =
      toFppfLQCohFbc X ⋙ FppfModules.LQCohFbc.toQCoh X := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh

namespace AlgebraicGeometry.AlgebraicStack

open AlgebraicGeometry.GroupoidsOver DerivedCategory

variable {S : Scheme.{u}}

/-- A single object in `D⁺(𝒪_X)` built from an fppf `LQCoh^{fbc}` module has
cohomology in `lqcohFbc`. -/
theorem singleFunctor_maps_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    FppfModules.lqcohFbc X ≤
      (Plus.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (DerivedCategory.Plus.singleFunctor (fppfModules X) n) := sorry

/-- Degree-`n` single-object functor into `D⁺_{LQCoh^{fbc}}(𝒪_X)`. -/
def DerivedLQCohFbc.Plus.singleFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    FppfModules.LQCohFbc X ⥤ DerivedLQCohFbc.Plus X :=
  FullSubcategory.restrict (DerivedCategory.Plus.singleFunctor (fppfModules X) n)
    (singleFunctor_maps_lqcohFbc X n)

/-- `DerivedLQCohFbc.Plus.singleFunctor` is the restriction of
`Plus.singleFunctor`. -/
theorem DerivedLQCohFbc.Plus.singleFunctor_eq (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    DerivedLQCohFbc.Plus.singleFunctor X n =
      FullSubcategory.restrict (DerivedCategory.Plus.singleFunctor (fppfModules X) n)
        (singleFunctor_maps_lqcohFbc X n) := sorry

namespace DerivedQCoh

/-- Place a quasi-coherent module in degree zero in `D⁺_QCoh(𝒪_X)`. -/
def singlePlus (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ DerivedQCoh.Plus X :=
  QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
    DerivedQCoh.Plus.quotientFunctor X

/-- `singlePlus` is the degree-zero plus single functor followed by the plus
quotient functor. -/
theorem singlePlus_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    singlePlus X =
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        DerivedQCoh.Plus.quotientFunctor X := sorry

/-- Reduce `H^i ∘ inclusion ∘ Rf_{QCoh,*} ∘ singlePlus` along
`pushforward_facIso`. -/
def homology_pushforward_single_pushforwardFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        pushforwardToPlus f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0)
    (isoWhiskerRight (pushforward_facIso f)
      (Plus.inclusion Y ⋙ homologyFunctor Y i))

/-- `homology_pushforward_single_pushforwardFac` is left whiskering of
`pushforward_facIso`. -/
theorem homology_pushforward_single_pushforwardFac_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    homology_pushforward_single_pushforwardFac f i =
      isoWhiskerLeft (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0)
        (isoWhiskerRight (pushforward_facIso f)
          (Plus.inclusion Y ⋙ homologyFunctor Y i)) := sorry

/-- Reduce the plus-quotient factorization of `Rf_{QCoh,*}` along
`Plus.inclusion_facIso`. -/
def homology_pushforward_single_inclusionFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        pushforwardToPlus f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ Plus.toUnboundedComposite Y ⋙
          homologyFunctor Y i :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f)
    (isoWhiskerRight (Plus.inclusion_facIso Y) (homologyFunctor Y i))

/-- `homology_pushforward_single_inclusionFac` is left whiskering of
`Plus.inclusion_facIso`. -/
theorem homology_pushforward_single_inclusionFac_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    homology_pushforward_single_inclusionFac f i =
      isoWhiskerLeft
        (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
          derivedPushforwardPlusLQCohFbc f)
        (isoWhiskerRight (Plus.inclusion_facIso Y) (homologyFunctor Y i)) :=
  sorry

/-- Reduce `H^i` along `homologyFunctor_comp_quotientFunctor`. -/
def homology_pushforward_single_homologyFac {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ Plus.toUnboundedComposite Y ⋙
          homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y i :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y)
    (homologyFunctor_comp_quotientFunctor Y i)

/-- `homology_pushforward_single_homologyFac` is left whiskering of
`homologyFunctor_comp_quotientFunctor`. -/
theorem homology_pushforward_single_homologyFac_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    homology_pushforward_single_homologyFac f i =
      isoWhiskerLeft
        (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
          derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y)
        (homologyFunctor_comp_quotientFunctor Y i) := sorry

/-- Composite of the three factorization comparisons reducing
`H^i ∘ inclusion ∘ Rf_{QCoh,*} ∘ singlePlus` to degree-zero homology of
plus `Rf_*` after `homologyToQCoh`. -/
def homology_pushforward_single_reduce {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙ homologyFunctor Y i ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y i :=
  homology_pushforward_single_pushforwardFac f i ≪≫
    homology_pushforward_single_inclusionFac f i ≪≫
    homology_pushforward_single_homologyFac f i

/-- `homology_pushforward_single_reduce` is the composite of the three
factorization comparisons. -/
theorem homology_pushforward_single_reduce_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℤ) :
    homology_pushforward_single_reduce f i =
      homology_pushforward_single_pushforwardFac f i ≪≫
        homology_pushforward_single_inclusionFac f i ≪≫
        homology_pushforward_single_homologyFac f i := sorry

/-- Degree-`i` homology of bounded-below fppf `Rf_*` on a degree-zero object is
the ordinary right-derived functor of module pushforward. -/
def modulePushforward_single_homologyIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
        moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i :=
  (isoWhiskerRight
      (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
        (moduleDerivedPushforwardPlus_comp_ι f))
      (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ))) ≪≫
    (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
      (isoWhiskerRight
        (Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso
          (FppfDerivedPushforwardImpl.modulePushforward f)).symm
        (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ)))) ≪≫
    Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
      (FppfDerivedPushforwardImpl.modulePushforward f) i

/-- The unbounded single-object homology comparison is the plus inclusion
comparison, the canonical model iso, and `degreeFunctorIsoRightDerived`. -/
theorem modulePushforward_single_homologyIso_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    modulePushforward_single_homologyIso f i =
      (isoWhiskerRight
          (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
            (moduleDerivedPushforwardPlus_comp_ι f))
          (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ))) ≪≫
        (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
          (isoWhiskerRight
            (Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso
              (FppfDerivedPushforwardImpl.modulePushforward f)).symm
            (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ)))) ≪≫
        Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
          (FppfDerivedPushforwardImpl.modulePushforward f) i := sorry

/-- Forgetful comparison of the plus `LQCoh^{fbc}` single functor with the
ambient plus single functor. -/
def DerivedLQCohFbc.Plus.singleFunctor_comp_inclusion (X : GroupoidsOver S)
    [AlgebraicStack X] (n : ℤ) :
    DerivedLQCohFbc.Plus.singleFunctor X n ⋙ DerivedLQCohFbc.Plus.inclusion X ≅
      FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) n :=
  FullSubcategory.restrict.compιIso
    (DerivedCategory.Plus.singleFunctor (fppfModules X) n)
    (singleFunctor_maps_lqcohFbc X n)

/-- Right-derived pushforward of a quasi-coherent fppf module remains in
fppf `LQCoh^{fbc}`. -/
theorem mem_rightDerived_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    FppfModules.lqcohFbc Y
      ((QCoh.inclusion X ⋙
          (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i).obj F) :=
  sorry

/-- Lift of ordinary fppf `R^i f_*` of a quasi-coherent module into fppf
`LQCoh^{fbc}`. -/
def rightDerivedLQCohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ FppfModules.LQCohFbc Y :=
  (FppfModules.lqcohFbc Y).lift
    (QCoh.inclusion X ⋙
      (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i)
    (mem_rightDerived_lqcohFbc f i)

/-- The underlying fppf module of `rightDerivedLQCohFbc` is ordinary
`R^i f_*`. -/
theorem rightDerivedLQCohFbc_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    rightDerivedLQCohFbc f i ⋙ FppfModules.inclusion Y =
      QCoh.inclusion X ⋙
        (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i :=
  rfl

/-- Forget lifted cohomology of plus `Rf_*` on a degree-zero object. -/
def homology_underlying_compι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ⋙
          FppfModules.inclusion Y ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).ι ⋙
            DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y)
    (DerivedCategory.CohomologyIn.Homology.compιIso
      (FppfModules.lqcohFbc Y) (i : ℤ))

/-- Replace `toUnbounded ⋙ cohomologyIn.ι` by the ambient plus inclusion. -/
def homology_underlying_toAmbient {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).ι ⋙
            DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ⋙
          DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
      derivedPushforwardPlusLQCohFbc f)
    (isoWhiskerRight
      (DerivedCategory.Plus.CohomologyIn.toUnbounded.compιIso
        (FppfModules.lqcohFbc Y))
      (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace plus `Rf_*` followed by the ambient inclusion with the plus-level
restriction comparison. -/
def homology_underlying_plusInclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ⋙
          DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft
    (QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0)
    (isoWhiskerRight (derivedPushforwardPlusLQCohFbc_comp_inclusion f)
      (DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace the plus `LQCoh^{fbc}` single functor by the ambient plus single
functor. -/
def homology_underlying_singleInclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        DerivedLQCohFbc.Plus.inclusion X ⋙ moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
          moduleDerivedPushforwardPlus f ⋙
            DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X)
    (isoWhiskerRight (DerivedLQCohFbc.Plus.singleFunctor_comp_inclusion X 0)
      (moduleDerivedPushforwardPlus f ⋙
        DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ)))

/-- Replace plus homology of `Rf_*` on a degree-zero object by ordinary
`R^i f_*`. -/
def homology_underlying_rightDerived {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X ⋙
        DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
          moduleDerivedPushforwardPlus f ⋙
            DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      QCoh.inclusion X ⋙
        (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i :=
  isoWhiskerLeft (QCoh.toFppfLQCohFbc X ⋙ FppfModules.inclusion X)
    (modulePushforward_single_homologyIso f i)

/-- Underlying comparison from plus `LQCoh^{fbc}` homology of `Rf_*` on a
degree-zero object to ordinary fppf `R^i f_*`. -/
def homology_fppfModuleDerivedPushforward_single_underlying
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ⋙
          FppfModules.inclusion Y ≅
      QCoh.inclusion X ⋙
        (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i :=
  homology_underlying_compι f i ≪≫
    homology_underlying_toAmbient f i ≪≫
    homology_underlying_plusInclusion f i ≪≫
    homology_underlying_singleInclusion f i ≪≫
    homology_underlying_rightDerived f i

/-- `rightDerivedLQCohFbc` is the lift of the underlying homology comparison
target. -/
def homology_fppfModuleDerivedPushforward_single_lqcoh
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          DerivedCategory.CohomologyIn.Homology.functor
            (FppfModules.lqcohFbc Y) (i : ℤ) ≅
      rightDerivedLQCohFbc f i :=
  (FppfModules.lqcohFbc Y).liftNatIso
    (fun F => ((DerivedCategory.CohomologyIn.Homology.functor
      (FppfModules.lqcohFbc Y) (i : ℤ)).obj
        ((QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
          derivedPushforwardPlusLQCohFbc f ⋙
            DerivedLQCohFbc.Plus.toUnbounded Y).obj F)).property)
    (mem_rightDerived_lqcohFbc f i)
    (homology_fppfModuleDerivedPushforward_single_underlying f i)

/-- Transported functor of Proposition 103.11.1 into the fppf Serre quotient
model of quasi-coherent cohomology. -/
def higherDirectImageToFppfQuotient {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ FppfModules.LQCohFbc.Quotient Y :=
  QCoh.higherDirectImageFunctor f i ⋙ QCoh.toFppfQuotient Y

/-- `higherDirectImageToFppfQuotient` is `R^i f_QCoh` followed by
`toFppfQuotient`. -/
theorem higherDirectImageToFppfQuotient_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    higherDirectImageToFppfQuotient f i =
      QCoh.higherDirectImageFunctor f i ⋙ QCoh.toFppfQuotient Y :=
  rfl

/-- Named bridge from degree-zero homology of fppf `Rf_*` after `toQCoh` to
ordinary fppf `R^i f_*` after `toQCoh`. -/
def homology_fppfModuleDerivedPushforward_single {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh.toFppfLQCohFbc X ⋙ DerivedLQCohFbc.Plus.singleFunctor X 0 ⋙
        derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.toUnbounded Y ⋙
          homologyToQCoh Y (i : ℤ) ≅
      rightDerivedLQCohFbc f i ⋙ FppfModules.LQCohFbc.toQCoh Y :=
  isoWhiskerRight (homology_fppfModuleDerivedPushforward_single_lqcoh f i)
    (FppfModules.LQCohFbc.toQCoh Y)

/-- `homology_fppfModuleDerivedPushforward_single` is lifted homology
postcomposed with `toQCoh`. -/
theorem homology_fppfModuleDerivedPushforward_single_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    homology_fppfModuleDerivedPushforward_single f i =
      isoWhiskerRight (homology_fppfModuleDerivedPushforward_single_lqcoh f i)
        (FppfModules.LQCohFbc.toQCoh Y) := sorry

/-- Restriction of fppf modules to étale modules is full: morphisms of sheaves
on the identity-on-objects comparison are morphisms of the underlying
presheaves. -/
instance restriction_full (X : GroupoidsOver S) : (restriction X).Full :=
  sorry

/-- Restriction of fppf modules to étale modules is additive. -/
instance restriction_additive (X : GroupoidsOver S) :
    (restriction X).Additive :=
  sorry

/-- The identity-on-objects comparison `ε : X_fppf ⟶ X_étale` is continuous. -/
instance etaleFppfHom_base_isContinuous (X : GroupoidsOver S) :
    (etaleFppfHom X).base.IsContinuous
      (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology :=
  (etaleFppfHom X).isMorphismOfSites.toIsContinuous

/-- Restriction of fppf modules to étale modules preserves homology. -/
instance restriction_preservesHomology (X : GroupoidsOver S) :
    (restriction X).PreservesHomology :=
  sorry

/-- Restriction of fppf modules to étale modules preserves injective objects. -/
instance restriction_preservesInjectiveObjects (X : GroupoidsOver S) :
    (restriction X).PreservesInjectiveObjects :=
  sorry

/-- Restriction of fppf `LQCoh^{fbc}` to étale `LQCoh^{fbc}`. -/
def restrictLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] :
    FppfModules.LQCohFbc X ⥤ LQCohFbc X where
  obj F := ⟨(restriction X).obj F.obj, F.property⟩
  map φ := ObjectProperty.homMk ((restriction X).map φ.hom)
  map_id := sorry
  map_comp := sorry

/-- `restrictLQCohFbc` is objectwise restriction of the underlying fppf
module. -/
theorem restrictLQCohFbc_obj_eq (X : GroupoidsOver S) [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    (restrictLQCohFbc X).obj F = ⟨(restriction X).obj F.obj, F.property⟩ :=
  rfl

/-- Quasi-coherent higher direct image obtained by applying étale `Q` to the
restriction of fppf `R^i f_*`. This is the restriction-of-fppf formula for
`R^i f_QCoh` from Proposition 103.11.1. -/
def higherDirectImageFromFppf {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ QCoh Y :=
  rightDerivedLQCohFbc f i ⋙ restrictLQCohFbc Y ⋙ LQCohFbc.toQCoh Y

/-- `higherDirectImageFromFppf` is restriction of fppf `R^i f_*` followed by
étale `Q`. -/
theorem higherDirectImageFromFppf_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    higherDirectImageFromFppf f i =
      rightDerivedLQCohFbc f i ⋙ restrictLQCohFbc Y ⋙ LQCohFbc.toQCoh Y :=
  rfl

/-- The adjunction counit `Q(restrict (R^i f_* F)) ⟶ R^i f_* F` of
Lemma 103.10.1, as a morphism of fppf modules. -/
def rightDerived_toQCohCounit {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    ((QCoh.toFppfLQCohFbc Y).obj ((higherDirectImageFromFppf f i).obj F)).obj ⟶
      ((rightDerivedLQCohFbc f i).obj F).obj :=
  (restriction Y).preimage
    ((LQCohFbc.inclusion Y).map
      ((QCoh.toLQCohFbc_isRightAdjoint_toQCoh Y).some.counit.app
        ((restrictLQCohFbc Y).obj ((rightDerivedLQCohFbc f i).obj F))))

/-- `rightDerived_toQCohCounit` is the fppf lift of the étale reflector
counit. -/
theorem rightDerived_toQCohCounit_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    rightDerived_toQCohCounit f i F =
      (restriction Y).preimage
        ((LQCohFbc.inclusion Y).map
          ((QCoh.toLQCohFbc_isRightAdjoint_toQCoh Y).some.counit.app
            ((restrictLQCohFbc Y).obj ((rightDerivedLQCohFbc f i).obj F)))) :=
  rfl

/-- After the Serre quotient `Q` that kills parasitic objects, the counit
comparing `Q(restrict (R^i f_* F))` with fppf `R^i f_* F` is an isomorphism. -/
instance rightDerived_toQCohCounit_map_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    IsIso
      ((FppfModules.LQCohFbc.toQCoh Y).map
        (ObjectProperty.homMk (rightDerived_toQCohCounit f i F))) :=
  sorry

/-- Equality of underlying section types of an fppf module and of its étale
restriction, after forgetting to type-valued presheaves. -/
theorem restriction_forget_sections_eq (X : GroupoidsOver S) (M : fppfModules X)
    (U : X.totalᵒᵖ) :
    ((sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf).obj ((restriction X).obj M))).obj U =
    ((sheafToPresheaf (fppfRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (fppfRingedSite X).structureSheaf).obj M)).obj U :=
  sorry

/-- Sections of a restricted fppf module, as a map of underlying types. -/
def restriction_forget_homApp (X : GroupoidsOver S) (M : fppfModules X)
    (U : X.totalᵒᵖ) :
    ((sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf).obj ((restriction X).obj M))).obj U ⟶
    ((sheafToPresheaf (fppfRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (fppfRingedSite X).structureSheaf).obj M)).obj U :=
  eqToHom (restriction_forget_sections_eq X M U)

/-- Inverse sections of a restricted fppf module, as a map of underlying types. -/
def restriction_forget_invApp (X : GroupoidsOver S) (M : fppfModules X)
    (U : X.totalᵒᵖ) :
    ((sheafToPresheaf (fppfRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (fppfRingedSite X).structureSheaf).obj M)).obj U ⟶
    ((sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf).obj ((restriction X).obj M))).obj U :=
  eqToHom (restriction_forget_sections_eq X M U).symm

/-- Forgetting after restriction of an fppf module recovers the underlying
type-valued fppf presheaf. -/
def restriction_forget_presheafIso (X : GroupoidsOver S) (M : fppfModules X) :
    (sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf).obj ((restriction X).obj M)) ≅
      (sheafToPresheaf (fppfRingedSite X).siteTopology (Type u)).obj
        ((Sheaf.InternalModule.ToInternal.underlying
          (fppfRingedSite X).structureSheaf).obj M) :=
  NatIso.ofComponents
    (fun U ↦
      { hom := restriction_forget_homApp X M U
        inv := restriction_forget_invApp X M U
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- Whiskering by the identity functor does not change type-valued presheaves. -/
def whiskeringLeft_id_op (C : Type (u + 1)) [Category.{u} C] :
    (whiskeringLeft Cᵒᵖ Cᵒᵖ (Type u)).obj (𝟭 C).op ≅ 𝟭 (Cᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents
    (fun P ↦
      { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }
        inv := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- Transport `restriction_forget_presheafIso` along the identity-on-objects
continuous pushforward. -/
def restriction_forget_presheafIso_continuous (X : GroupoidsOver S)
    (M : fppfModules X) :
    (sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
      ((Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf).obj ((restriction X).obj M)) ≅
      (sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
        (((etaleFppfHom X).base.sheafPushforwardContinuous (Type u)
            (etaleRingedSite X).siteTopology
            (fppfRingedSite X).siteTopology).obj
          ((Sheaf.InternalModule.ToInternal.underlying
            (fppfRingedSite X).structureSheaf).obj M)) :=
  restriction_forget_presheafIso X M ≪≫
    (whiskeringLeft_id_op X.total).symm.app
      ((sheafToPresheaf (fppfRingedSite X).siteTopology (Type u)).obj
        ((Sheaf.InternalModule.ToInternal.underlying
          (fppfRingedSite X).structureSheaf).obj M)) ≪≫
    ((etaleFppfHom X).base.sheafPushforwardContinuousCompSheafToPresheafIso
      (Type u) (etaleRingedSite X).siteTopology
      (fppfRingedSite X).siteTopology).symm.app
      ((Sheaf.InternalModule.ToInternal.underlying
        (fppfRingedSite X).structureSheaf).obj M)

/-- `restriction_forget_presheafIso` is identity on sections. -/
theorem restriction_forget_presheafIso_eq (X : GroupoidsOver S)
    (M : fppfModules X) (U : X.totalᵒᵖ)
    (x :
      ((sheafToPresheaf (etaleRingedSite X).siteTopology (Type u)).obj
        ((Sheaf.InternalModule.ToInternal.underlying
          (etaleRingedSite X).structureSheaf).obj
          ((restriction X).obj M))).obj U) :
    (restriction_forget_presheafIso X M).hom.app U x = x :=
  sorry

/-- Restriction of fppf modules forgets to continuous pushforward of the
underlying type-valued sheaf along `etaleFppfHom`. -/
def restriction_forgetIso (X : GroupoidsOver S) :
    restriction X ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite X).structureSheaf ≅
      Sheaf.InternalModule.ToInternal.underlying
          (fppfRingedSite X).structureSheaf ⋙
        (etaleFppfHom X).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology :=
  NatIso.ofComponents
    (fun M ↦
      (fullyFaithfulSheafToPresheaf
        (etaleRingedSite X).siteTopology (Type u)).preimageIso
        (restriction_forget_presheafIso_continuous X M))
    (fun _ ↦ sorry)

/-- `restriction_forgetIso` is the sheafification of
`restriction_forget_presheafIso_continuous`. -/
theorem restriction_forgetIso_eq (X : GroupoidsOver S) (M : fppfModules X) :
    (restriction_forgetIso X).app M =
      (fullyFaithfulSheafToPresheaf
        (etaleRingedSite X).siteTopology (Type u)).preimageIso
        (restriction_forget_presheafIso_continuous X M) :=
  sorry

/-- The left-hand type-valued composite `f_{fppf,*} ⋙ ε_*` forgets to
right Kan extension of the underlying presheaf. -/
def restriction_pushforward_typeSquare_left {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardCocontinuous (Type u)
          (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology ⋙
        (etaleFppfHom Y).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite Y).siteTopology (fppfRingedSite Y).siteTopology) ⋙
      sheafToPresheaf (etaleRingedSite Y).siteTopology (Type u) ≅
      sheafToPresheaf (fppfRingedSite X).siteTopology (Type u) ⋙
        (toFunctor f).op.ran :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      ((etaleFppfHom Y).base.sheafPushforwardContinuousCompSheafToPresheafIso
        (Type u) (etaleRingedSite Y).siteTopology
        (fppfRingedSite Y).siteTopology) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((toFunctor f).sheafPushforwardCocontinuousCompSheafToPresheafIso
        (Type u) (fppfRingedSite X).siteTopology
        (fppfRingedSite Y).siteTopology)
      ((whiskeringLeft _ _ (Type u)).obj (etaleFppfHom Y).base.op) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf (fppfRingedSite X).siteTopology (Type u))
      (isoWhiskerLeft ((toFunctor f).op.ran) (whiskeringLeft_id_op Y.total) ≪≫
        ((toFunctor f).op.ran).rightUnitor)

/-- The right-hand type-valued composite `ε_* ⋙ f_{étale,*}` forgets to
right Kan extension of the underlying presheaf. -/
def restriction_pushforward_typeSquare_right {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    ((etaleFppfHom X).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology ⋙
        (toFunctor f).sheafPushforwardCocontinuous (Type u)
          (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology) ⋙
      sheafToPresheaf (etaleRingedSite Y).siteTopology (Type u) ≅
      sheafToPresheaf (fppfRingedSite X).siteTopology (Type u) ⋙
        (toFunctor f).op.ran :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      ((toFunctor f).sheafPushforwardCocontinuousCompSheafToPresheafIso
        (Type u) (etaleRingedSite X).siteTopology
        (etaleRingedSite Y).siteTopology) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((etaleFppfHom X).base.sheafPushforwardContinuousCompSheafToPresheafIso
        (Type u) (etaleRingedSite X).siteTopology
        (fppfRingedSite X).siteTopology)
      ((toFunctor f).op.ran) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf (fppfRingedSite X).siteTopology (Type u))
      (isoWhiskerRight (whiskeringLeft_id_op X.total) ((toFunctor f).op.ran) ≪≫
        ((toFunctor f).op.ran).leftUnitor)

/-- The type-valued site square `f_{fppf,*} ⋙ ε_* ≅ ε_* ⋙ f_{étale,*}` after
forgetting to presheaves. -/
def restriction_pushforward_typeSquare_presheaf {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardCocontinuous (Type u)
          (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology ⋙
        (etaleFppfHom Y).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite Y).siteTopology (fppfRingedSite Y).siteTopology) ⋙
      sheafToPresheaf (etaleRingedSite Y).siteTopology (Type u) ≅
      ((etaleFppfHom X).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology ⋙
        (toFunctor f).sheafPushforwardCocontinuous (Type u)
          (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology) ⋙
        sheafToPresheaf (etaleRingedSite Y).siteTopology (Type u) :=
  restriction_pushforward_typeSquare_left f ≪≫
    (restriction_pushforward_typeSquare_right f).symm

/-- The type-valued site square `f_{fppf,*} ⋙ ε_* ≅ ε_* ⋙ f_{étale,*}`. -/
def restriction_pushforward_typeSquare {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology ⋙
      (etaleFppfHom Y).base.sheafPushforwardContinuous (Type u)
        (etaleRingedSite Y).siteTopology (fppfRingedSite Y).siteTopology ≅
      (etaleFppfHom X).base.sheafPushforwardContinuous (Type u)
          (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology ⋙
        (toFunctor f).sheafPushforwardCocontinuous (Type u)
          (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (etaleRingedSite Y).siteTopology (Type u))
    (restriction_pushforward_typeSquare_presheaf f)

/-- Underlying type-valued sheaves of the two underived composites
`f_{fppf,*} ⋙ ε_*` and `ε_* ⋙ f_{étale,*}`. -/
def restriction_modulePushforward_typeIso {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    FppfDerivedPushforwardImpl.modulePushforward f ⋙ restriction Y ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (etaleRingedSite Y).structureSheaf ≅
      restriction X ⋙ moduleDirectImage f ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (etaleRingedSite Y).structureSheaf :=
  isoWhiskerLeft (FppfDerivedPushforwardImpl.modulePushforward f)
      (restriction_forgetIso Y) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerRight
      (RingedSite.ToposHom.ModulePushforward.forgetIso
        (FppfDerivedPushforwardImpl.fppfRingedToposHom f))
      ((etaleFppfHom Y).base.sheafPushforwardContinuous (Type u)
        (etaleRingedSite Y).siteTopology (fppfRingedSite Y).siteTopology) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (fppfRingedSite X).structureSheaf)
      (restriction_pushforward_typeSquare f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (restriction_forgetIso X).symm
      ((toFunctor f).sheafPushforwardCocontinuous (Type u)
        (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (restriction X)
      (RingedSite.ToposHom.ModulePushforward.forgetIso
        (moduleDirectImageToposHom f)).symm

/-- Underived isomorphism `f_{fppf,*} ⋙ ε_* ≅ ε_* ⋙ f_{étale,*}`. -/
def restriction_modulePushforward_iso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    FppfDerivedPushforwardImpl.modulePushforward f ⋙ restriction Y ≅
      restriction X ⋙ moduleDirectImage f :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying
            (etaleRingedSite Y).structureSheaf
            ((restriction_modulePushforward_typeIso f).hom.app M) sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying
            (etaleRingedSite Y).structureSheaf
            ((restriction_modulePushforward_typeIso f).inv.app M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- `restriction_modulePushforward_iso` is the module lift of
`restriction_modulePushforward_typeIso`. -/
theorem restriction_modulePushforward_iso_hom_app {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (M : fppfModules X) :
    (Sheaf.InternalModule.ToInternal.underlying
        (etaleRingedSite Y).structureSheaf).map
      ((restriction_modulePushforward_iso f).hom.app M) =
      (restriction_modulePushforward_typeIso f).hom.app M :=
  sorry

/-- Specified comparison of ordinary right-derived functors obtained by
postcomposition with restriction, deriving the underived site square, and
precomposition with restriction. -/
def restriction_rightDerived_iso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    (FppfDerivedPushforwardImpl.modulePushforward f).rightDerived i ⋙
        restriction Y ≅
      restriction X ⋙ (moduleDirectImage f).rightDerived i :=
  (Functor.RightDerived.postcompIso
      (FppfDerivedPushforwardImpl.modulePushforward f) (restriction Y) i).symm ≪≫
    NatIso.rightDerived (restriction_modulePushforward_iso f) i ≪≫
    Functor.RightDerived.precompIso (restriction X) (moduleDirectImage f) i

/-- `restriction_rightDerived_iso` is `postcompIso`, `NatIso.rightDerived` of
the underived site square, and `precompIso`. -/
theorem restriction_rightDerived_iso_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    restriction_rightDerived_iso f i =
      (Functor.RightDerived.postcompIso
          (FppfDerivedPushforwardImpl.modulePushforward f) (restriction Y) i).symm ≪≫
        NatIso.rightDerived (restriction_modulePushforward_iso f) i ≪≫
        Functor.RightDerived.precompIso (restriction X) (moduleDirectImage f) i :=
  sorry

/-- The fppf lift of the étale comparison of `R^i f_QCoh` with restricted fppf
`R^i f_*`. -/
def rightDerived_toHigherDirectImage_hom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    ((QCoh.toFppfLQCohFbc Y).obj ((QCoh.higherDirectImageFunctor f i).obj F)).obj ⟶
      ((rightDerivedLQCohFbc f i).obj F).obj :=
  (restriction Y).preimage
    (((LQCohFbc.inclusion Y).map
        ((QCoh.toLQCohFbc_isRightAdjoint_toQCoh Y).some.counit.app
          ((LQCohFbc.higherDirectImageFunctor f i).obj
            ((QCoh.toLQCohFbc X).obj F)))) ≫
      (restriction_rightDerived_iso f i).inv.app ((QCoh.inclusion X).obj F))

/-- `rightDerived_toHigherDirectImage_hom` is the fppf lift of the étale
reflector counit followed by the inverse of `restriction_rightDerived_iso`. -/
theorem rightDerived_toHigherDirectImage_hom_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    rightDerived_toHigherDirectImage_hom f i F =
      (restriction Y).preimage
        (((LQCohFbc.inclusion Y).map
            ((QCoh.toLQCohFbc_isRightAdjoint_toQCoh Y).some.counit.app
              ((LQCohFbc.higherDirectImageFunctor f i).obj
                ((QCoh.toLQCohFbc X).obj F)))) ≫
          (restriction_rightDerived_iso f i).inv.app
            ((QCoh.inclusion X).obj F)) :=
  rfl

/-- After the Serre quotient that kills parasitic objects, the comparison of
`R^i f_QCoh` with fppf `R^i f_*` is an isomorphism. -/
instance rightDerived_toHigherDirectImage_hom_map_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    IsIso
      ((FppfModules.LQCohFbc.toQCoh Y).map
        (ObjectProperty.homMk (rightDerived_toHigherDirectImage_hom f i F))) :=
  sorry

/-- Specified natural comparison from fppf `R^i f_*` after `toQCoh` to
`R^i f_QCoh` of Proposition 103.11.1 after `toFppfQuotient`. -/
def homology_pushforward_single_iso_higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    rightDerivedLQCohFbc f i ⋙ FppfModules.LQCohFbc.toQCoh Y ≅
      higherDirectImageToFppfQuotient f i :=
  NatIso.ofComponents
    (fun F ↦
      (asIso
        ((FppfModules.LQCohFbc.toQCoh Y).map
          (ObjectProperty.homMk
            (rightDerived_toHigherDirectImage_hom f i F)))).symm)
    (fun _ ↦ sorry)

/-- `homology_pushforward_single_iso_higherDirectImage` is the Serre quotient
of `rightDerived_toHigherDirectImage_hom`. -/
theorem homology_pushforward_single_iso_higherDirectImage_eq
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    (homology_pushforward_single_iso_higherDirectImage f i).inv.app =
      fun F ↦
        (FppfModules.LQCohFbc.toQCoh Y).map
          (ObjectProperty.homMk (rightDerived_toHigherDirectImage_hom f i F)) :=
  sorry

/-- Canonical identification of `H^i ∘ Rf_{QCoh,*} ∘ singlePlus` with
`R^i f_QCoh` of Proposition 103.11.1 after `toFppfQuotient`. -/
def homology_pushforward_single_iso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙
        homologyFunctor Y (i : ℤ) ≅
      QCoh.higherDirectImageFunctor f i ⋙ QCoh.toFppfQuotient Y :=
  homology_pushforward_single_reduce f i ≪≫
    homology_fppfModuleDerivedPushforward_single f i ≪≫
    homology_pushforward_single_iso_higherDirectImage f i

/-- `homology_pushforward_single_iso` is the factorization reduction, the
unbounded fppf homology bridge, and the specified comparison with
`QCoh.higherDirectImageFunctor` after `toFppfQuotient`. -/
theorem homology_pushforward_single_iso_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    homology_pushforward_single_iso f i =
      homology_pushforward_single_reduce f i ≪≫
        homology_fppfModuleDerivedPushforward_single f i ≪≫
        homology_pushforward_single_iso_higherDirectImage f i := sorry

/-- After `toFppfQuotient`, `H^i ∘ Rf_{QCoh,*} ∘ singlePlus` agrees with
`R^i f_QCoh` of Proposition 103.11.1. -/
theorem homology_pushforward_single_iso_higherDirectImageFunctor
    {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    IsIsomorphic
      ((singlePlus X ⋙ pushforward f ⋙ Plus.inclusion Y ⋙
          homologyFunctor Y (i : ℤ)).obj F)
      ((QCoh.higherDirectImageFunctor f i ⋙ QCoh.toFppfQuotient Y).obj F) :=
  sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack
