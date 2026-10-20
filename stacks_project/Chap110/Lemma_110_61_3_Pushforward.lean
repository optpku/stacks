module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Unbounded fppf-module derived pushforward on algebraic stacks

A 1-morphism of algebraic stacks induces a morphism of fppf ringed topoi and
the associated unbounded derived direct image on `D(𝒪)`. Preservation of
`D_{LQCoh^{fbc}}` is recorded as a mapsTo predicate, matching the scheme-level
`pushforwardCohomologyIn.mapsTo` pattern. The ambient of `DerivedQCoh` in this
library is the fppf derived category, matching the Stacks convention that
`Mod(𝒪_X)` is formed on the big fppf site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open CategoryTheory.ObjectProperty ComplexShape
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

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
instance toFunctor_op_hasPointwiseRightKanExtension_type
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

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidsOver

variable {S : Scheme.{u}}

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
fibred in groupoids. Assembled at coefficient universe `u` matching
`fppfRingedSite`, so that `ToposHom.modulePushforward` lands in
`fppfModules`. -/
def fppfRingedToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (fppfRingedSite X) (fppfRingedSite Y) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (fppfRingedSite X) (fppfRingedSite Y) (toFunctor f) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (fppfStructureSheafInversePresheaf f)

/-- The underlying topos morphism of `fppfRingedToposHom` is the cocontinuous
geometric morphism of fppf sites. -/
theorem fppfRingedToposHom_toTopos {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (fppfRingedToposHom f).toTopos =
      (toFunctor f).morphismOfTopoiInOfCocontinuous
        (fppfRingedSite X).siteTopology (fppfRingedSite Y).siteTopology :=
  sorry

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

/-- Unbounded derived pushforward `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of fppf modules
along a 1-morphism of algebraic stacks. -/
noncomputable abbrev moduleDerivedPushforward {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.RightDerived.KInjective.functor (modulePushforward f)

/-- Unbounded derived fppf-module pushforward preserves
`D_{LQCoh^{fbc}}`. This is the mapsTo predicate whose restriction would induce
`Rf_* : DerivedQCoh X ⥤ DerivedQCoh Y`. -/
def mapsDerivedLQCohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) ≤
    (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)).inverseImage
      (moduleDerivedPushforward f)

/-- Unfold `mapsDerivedLQCohFbc` as preservation of `lqcohFbc`-cohomology under
`moduleDerivedPushforward`. -/
theorem mapsDerivedLQCohFbc_iff {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    mapsDerivedLQCohFbc f ↔
      ∀ E : ModuleDerived X,
        DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) E →
          DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y)
            ((moduleDerivedPushforward f).obj E) := sorry

end AlgebraicGeometry.AlgebraicStack
