/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small.RingedTopos
public import stacks_project.Chap96.«96_9_4_1_Comparison»
public import stacks_project.Chap104.Proposition_104_8_4_Sites
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact

/-!
# The `u+1` module model of the actual parasitic Verdier quotient

The base schemes remain in `u`. Coefficient rings and module section carriers
are both in `u+1`, as for the established `QC(X)` owner. Local quasi-coherence
uses the existing lifted small-étale restrictions. Flat base change is the
small-étale comparison `c_φ` obtained from cartesian fill-ins, for every
morphism of `X` lying over a flat scheme map. No smallness of an arbitrary
module section carrier is imposed.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty CategoryTheory.Limits Opposite
open FiberedCategoryOver.Groupoids RingedSite.Hom
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- Fppf module sheaves with the same carrier universe as `QC(X)`. -/
abbrev LiftedFppfModules := RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)

/-- The two lifted coefficient presentations agree by the actual identity
maps of global-section rings. -/
def liftedEtaleToFppfCoefficients :
    (commEtaleRingedSiteLift X).structureSheaf.obj ⟶
      (liftedFppfStructureSheaf X).obj where
  app _ := 𝟙 _
  naturality := by intros; rfl

/-- The fppf sheaf condition implies the étale sheaf condition after this
identity-on-carriers coefficient restriction. -/
theorem liftedRestriction_isSheaf (M : LiftedFppfModules X) :
    Presheaf.IsSheaf X.etaleTopology
      ((PresheafOfModules.restrictScalars (liftedEtaleToFppfCoefficients X)).obj
        M.val).presheaf := sorry

/-- Actual restriction from fppf to étale modules; all section carriers and
restriction maps are retained. -/
def liftedFppfToEtale : LiftedFppfModules X ⥤
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) where
  obj M := ⟨(PresheafOfModules.restrictScalars (liftedEtaleToFppfCoefficients X)).obj M.val,
    liftedRestriction_isSheaf X M⟩
  map f := ⟨(PresheafOfModules.restrictScalars (liftedEtaleToFppfCoefficients X)).map f.val⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- These are lifted global-section rings, with their genuine commutative
ring structure. -/
instance liftedFppfCoeffCommRing (x : X.totalᵒᵖ) :
    CommRing ((liftedFppfStructureSheaf X).obj.obj x) := by
  change CommRing (ULift.{u + 1} Γ((X.p.obj x.unop).left, ⊤))
  infer_instance

/-- The affine tensor comparison sends `1 ⊗ m` to the actual restriction of `m`.
This is the source's Step 1 test on affine objects, not the definition of
`LQCoh^{fbc}`. -/
def liftedModuleBaseChange (M : LiftedFppfModules X) {x y : X.total} (φ : x ⟶ y) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (((liftedFppfStructureSheaf X).obj.map φ.op).hom)).obj
        (M.val.obj (op y)) ⟶ M.val.obj (op x) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (((liftedFppfStructureSheaf X).obj.map φ.op).hom)).homEquiv _ _).symm
    (M.val.map φ.op)

/-- Affine-chart tensor form of base change, retained only as the Step 1
companion of the image of `QC`. -/
def liftedFlatBaseChange (M : LiftedFppfModules X) : Prop :=
  ∀ {x y : X.total} (φ : x ⟶ y),
    IsAffine (X.p.obj x).left → IsAffine (X.p.obj y).left →
      AlgebraicGeometry.Flat (X.p.map φ).left → IsIso (liftedModuleBaseChange X M φ)

/-- Direct image of modules along a lifted small-étale ringed morphism has its
canonical inverse-image left adjoint. -/
instance liftedRingedHom_modulePushforward_isRightAdjoint
    {U V : Scheme.{u}} (f : U ⟶ V) :
    ((Scheme.Etale.Small.liftedRingedHom f).modulePushforward.{u + 1}).IsRightAdjoint :=
  sorry

/-- Universe-lifted ring map `𝒪_{U_étale}(W) ⟶ 𝒪_X(cartesianLift x W)`. -/
def restrictRingHomLift {x : X.total} (W : (X.p.obj x).left.Etale) :
    (Scheme.Etale.Small.liftedStructureSheaf (X.p.obj x).left).obj.obj (op W) ⟶
      (commEtaleRingedSiteLift X).structureSheaf.obj.obj (op (cartesianLift x W)) :=
  RingCat.ofHom
    { toFun := fun r ↦ ULift.up ((restrictRingHom x W).hom (ULift.down r))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Unfolding of `restrictRingHomLift` as the universe lift of `restrictRingHom`. -/
theorem restrictRingHomLift_apply {x : X.total}
    (W : (X.p.obj x).left.Etale)
    (r : (Scheme.Etale.Small.liftedStructureSheaf (X.p.obj x).left).obj.obj (op W)) :
    (restrictRingHomLift X W).hom r =
      ULift.up ((restrictRingHom x W).hom (ULift.down r)) := sorry

/-- The ring presheaf on `U_étale` with value the lifted `𝒪_X` at cartesian lifts. -/
def restrictEtaleRingLift (x : X.total) :
    ((X.p.obj x).left.Etale)ᵒᵖ ⥤ RingCat.{u + 1} where
  obj W := (commEtaleRingedSiteLift X).structureSheaf.obj.obj (op (cartesianLift x W.unop))
  map f := (commEtaleRingedSiteLift X).structureSheaf.obj.map (cartesianLiftMap x f.unop).op
  map_id := sorry
  map_comp := sorry

/-- Unfolding of `restrictEtaleRingLift` on an étale object. -/
theorem restrictEtaleRingLift_obj (x : X.total) (W : (X.p.obj x).left.Etale) :
    (restrictEtaleRingLift X x).obj (op W) =
      (commEtaleRingedSiteLift X).structureSheaf.obj.obj (op (cartesianLift x W)) := sorry

/-- `F` evaluated at cartesian lifts of `x`, as a presheaf of modules over
`restrictEtaleRingLift x`. -/
def restrictEtaleModulesLift
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) (x : X.total) :
    PresheafOfModules.{u + 1} (restrictEtaleRingLift X x) where
  obj W := F.val.obj (op (cartesianLift x W.unop))
  map f := F.val.map (cartesianLiftMap x f.unop).op
  map_id := sorry
  map_comp := sorry

/-- Unfolding of `restrictEtaleModulesLift` on an étale object. -/
theorem restrictEtaleModulesLift_obj
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (restrictEtaleModulesLift X F x).obj (op W) =
      F.val.obj (op (cartesianLift x W)) := sorry

/-- The natural map of ring presheaves `𝒪_{U_étale} ⟶ restrictEtaleRingLift x`. -/
def restrictRingNatTransLift (x : X.total) :
    (Scheme.Etale.Small.liftedStructureSheaf (X.p.obj x).left).obj ⟶
      restrictEtaleRingLift X x where
  app W := restrictRingHomLift X (x := x) W.unop
  naturality := sorry

/-- Components of `restrictRingNatTransLift` are `restrictRingHomLift`. -/
theorem restrictRingNatTransLift_app (x : X.total) (W : (X.p.obj x).left.Etale) :
    (restrictRingNatTransLift X x).app (op W) =
      restrictRingHomLift X (x := x) W := sorry

/-- The small-étale restriction `F|_{U_étale}` as a sheaf of lifted
`𝒪_{U_étale}`-modules, by cartesian-lift evaluation. -/
def restrictEtaleLift
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) (x : X.total) :
    RingedSite.ModuleCat.{u + 1}
      (Scheme.Etale.Small.liftedRingedSite (X.p.obj x).left) where
  val :=
    (PresheafOfModules.restrictScalars (restrictRingNatTransLift X x)).obj
      (restrictEtaleModulesLift X F x)
  isSheaf := sorry

/-- At `W` étale over `U`, the value of `restrictEtaleLift F x` is `F` at a
cartesian lift of `x`, with scalars restricted along `restrictRingHomLift`. -/
theorem restrictEtaleLift_obj
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (restrictEtaleLift X F x).val.obj (op W) =
      (ModuleCat.restrictScalars (restrictRingHomLift X (x := x) W).hom).obj
        (F.val.obj (op (cartesianLift x W))) := sorry

/-- Compatibility of the lifted cartesian fill-in with small-étale structure
maps: `φring.comp αy = αx.comp a_small^♯`. -/
theorem restrictRingHomLift_fillIn {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    ((commEtaleRingedSiteLift X).structureSheaf.obj.map (fillIn φ V').op).hom.comp
        (restrictRingHomLift X (x := y) V').hom =
      (restrictRingHomLift X (x := x)
          ((Scheme.smallEtalePullback (X.p.map φ).left).obj V')).hom.comp
        ((Scheme.Etale.Small.liftedRingedHom (X.p.map φ).left).structureSheafMap.hom.app
          (op V')).hom := sorry

/-- The push-form comparison
`c_φ : F|_{V_étale} ⟶ a_small,*(F|_{U_étale})` of lifted `𝒪_{V_étale}`-modules,
with components `F(φ')` on cartesian fill-ins. -/
def liftedModuleComparisonPushforward {x y : X.total} (φ : x ⟶ y)
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :
    restrictEtaleLift X F y ⟶
      ((Scheme.Etale.Small.liftedRingedHom (X.p.map φ).left).modulePushforward.{u + 1}).obj
        (restrictEtaleLift X F x) where
  val :=
    { app := fun V' ↦
        let a := (X.p.map φ).left
        let U' := (Scheme.smallEtalePullback a).obj V'.unop
        let αy := (restrictRingHomLift X (x := y) V'.unop).hom
        let αx := (restrictRingHomLift X (x := x) U').hom
        let φring :=
          ((commEtaleRingedSiteLift X).structureSheaf.obj.map (fillIn φ V'.unop).op).hom
        let aSharp :=
          ((Scheme.Etale.Small.liftedRingedHom a).structureSheafMap.hom.app V').hom
        (ModuleCat.restrictScalars αy).map (F.val.map (fillIn φ V'.unop).op) ≫
          (ModuleCat.restrictScalarsComp'App αy φring (φring.comp αy) rfl _).inv ≫
            (ModuleCat.restrictScalarsCongr
                (restrictRingHomLift_fillIn X φ V'.unop)).hom.app _ ≫
              (ModuleCat.restrictScalarsComp'App aSharp αx (αx.comp aSharp) rfl _).hom
      naturality := sorry }

/-- On an étale object `V' ⟶ V`, the push-form comparison has the same
underlying abelian map as `F(φ')`. -/
theorem liftedModuleComparisonPushforward_app {x y : X.total} (φ : x ⟶ y)
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    (V' : (X.p.obj y).left.Etale) (m : (restrictEtaleLift X F y).val.obj (op V')) :
    (liftedModuleComparisonPushforward X φ F).val.app (op V') m =
      (F.val.map (fillIn φ V').op).hom m := sorry

/-- The small-étale comparison
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` of lifted `𝒪_{U_étale}`-modules,
obtained as the adjunct of `liftedModuleComparisonPushforward`. -/
def liftedModuleComparison {x y : X.total} (φ : x ⟶ y)
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :
    ((Scheme.Etale.Small.liftedRingedHom (X.p.map φ).left).modulePullback.{u + 1}).obj
        (restrictEtaleLift X F y) ⟶
      restrictEtaleLift X F x :=
  (modulePullbackHomEquiv (Scheme.Etale.Small.liftedRingedHom (X.p.map φ).left)
      (restrictEtaleLift X F y) (restrictEtaleLift X F x)).symm
    (liftedModuleComparisonPushforward X φ F)

/-- `liftedModuleComparison φ F` is the adjunct of
`liftedModuleComparisonPushforward φ F`. -/
theorem liftedModuleComparison_adjunct {x y : X.total} (φ : x ⟶ y)
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :
    modulePullbackHomEquiv (Scheme.Etale.Small.liftedRingedHom (X.p.map φ).left)
        (restrictEtaleLift X F y) (restrictEtaleLift X F x)
        (liftedModuleComparison X φ F) =
      liftedModuleComparisonPushforward X φ F := sorry

/-- A lifted étale `𝒪_X`-module has the flat base change property if `c_φ` is
an isomorphism whenever `φ` lies over a flat morphism of schemes. -/
@[mk_iff]
class HasFlatBaseChangeLift
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) : Prop where
  /-- The comparison `c_φ` is an isomorphism along every flat lying-over morphism. -/
  comparison_isIso : ∀ {x y : X.total} (φ : x ⟶ y),
    AlgebraicGeometry.Flat (X.p.map φ).left → IsIso (liftedModuleComparison X φ F)

/-- Source-semantic characterisation: `c_φ` is an isomorphism whenever the
scheme morphism underlying `φ` is flat. -/
theorem hasFlatBaseChangeLift_spec
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :
    HasFlatBaseChangeLift X F ↔
      ∀ {x y : X.total} (φ : x ⟶ y),
        AlgebraicGeometry.Flat (X.p.map φ).left →
          IsIso (liftedModuleComparison X φ F) := sorry

/-- The lifted étale structure sheaf has the flat base change property. -/
instance instHasFlatBaseChangeLiftUnit :
    HasFlatBaseChangeLift X
      (SheafOfModules.unit (commEtaleRingedSiteLift X).structureSheaf) := sorry

/-- The comparison `c_φ` is an isomorphism when `F` has lifted flat base change
and `φ` lies over a flat morphism. -/
instance instLiftedModuleComparisonIsIso
    {F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)}
    [hF : HasFlatBaseChangeLift X F] {x y : X.total} (φ : x ⟶ y)
    [hflat : AlgebraicGeometry.Flat (X.p.map φ).left] :
    IsIso (liftedModuleComparison X φ F) :=
  hF.comparison_isIso φ hflat

/-- The object property of lifted étale `𝒪_X`-modules with the flat base change
property. -/
abbrev hasFlatBaseChangeLift :
    ObjectProperty (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :=
  HasFlatBaseChangeLift X

/-- Membership in `hasFlatBaseChangeLift X` is the class `HasFlatBaseChangeLift`. -/
theorem mem_hasFlatBaseChangeLift
    (F : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :
    hasFlatBaseChangeLift X F ↔ HasFlatBaseChangeLift X F := sorry

/-- Locally quasi-coherent lifted étale modules with the flat base change
property. -/
abbrev liftedEtaleLqcohFbc :
    ObjectProperty (RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)) :=
  IsLocallyQuasiCoherentLift ⊓ HasFlatBaseChangeLift X

/-- The object property of fppf modules whose étale restriction is locally
quasi-coherent and has small-étale flat base change. -/
def liftedLqcohFbc : ObjectProperty (LiftedFppfModules X) :=
  (liftedEtaleLqcohFbc X).inverseImage (liftedFppfToEtale X)

/-- An fppf module lies in `liftedLqcohFbc` iff its étale restriction is
locally quasi-coherent and has the small-étale flat base change property. -/
theorem liftedLqcohFbc_iff (M : LiftedFppfModules X) :
    liftedLqcohFbc X M ↔
      IsLocallyQuasiCoherentLift ((liftedFppfToEtale X).obj M) ∧
        HasFlatBaseChangeLift X ((liftedFppfToEtale X).obj M) := sorry

/-- `liftedLqcohFbc` is the inverse image of lifted étale `LQCoh^{fbc}` along
`liftedFppfToEtale`. -/
theorem liftedLqcohFbc_eq :
    liftedLqcohFbc X = (liftedEtaleLqcohFbc X).inverseImage (liftedFppfToEtale X) := sorry

/-- Parasitic vanishing on flat objects, with no section-size restriction. -/
def liftedParasiticModules : ObjectProperty (LiftedFppfModules X) :=
  fun M => ∀ {U : Over S} (x : X.p.Fiber U),
    AlgebraicStack.Flat (YonedaSlice.representative x) →
      IsZero (M.val.obj (op (CategoryTheory.Functor.Fiber.fiberInclusion.obj x)))

/-- The standard derived-category construction at the larger carrier universe. -/
instance liftedFppfModulesHasDerivedCategory :
    HasDerivedCategory.{u + 2} (LiftedFppfModules X) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (liftedFppfRingedSite X)

/-- The ambient derived category at the same universe as `QC(X)`. -/
abbrev LiftedModuleDerived := DerivedCategory (LiftedFppfModules X)

/-- The cohomology-in subcategory for the genuine lifted `LQCoh^{fbc}` property. -/
abbrev LiftedDerivedLQCohFbc := DerivedCategory.CohomologyIn (liftedLqcohFbc X)

/-- Lifted `LQCoh^{fbc}` is a weak Serre class. -/
instance liftedLqcohFbc_isWeakSerreClass : IsWeakSerreClass (liftedLqcohFbc X) := sorry

/-- Cohomology in lifted `LQCoh^{fbc}` is a triangulated subcategory. -/
instance liftedDerivedLQCohFbc_isTriangulated :
    (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).IsTriangulated :=
  inferInstance

/-- Forget only the cohomology-in proof. -/
abbrev LiftedDerivedLQCohFbc.inclusion :
    LiftedDerivedLQCohFbc X ⥤ LiftedModuleDerived X :=
  (DerivedCategory.cohomologyIn (liftedLqcohFbc X)).ι

/-- The actual parasitic cohomology subcategory of lifted `D_LQCoh^{fbc}`. -/
abbrev liftedDerivedParasitic : ObjectProperty (LiftedDerivedLQCohFbc X) :=
  (DerivedCategory.cohomologyIn (liftedParasiticModules X)).inverseImage
    (LiftedDerivedLQCohFbc.inclusion X)

/-- Parasitic cohomology in lifted `D_LQCoh^{fbc}` is triangulated. -/
instance liftedDerivedParasitic_isTriangulated :
    (liftedDerivedParasitic X).IsTriangulated := sorry

/-- The `u+1` model of the source's Verdier quotient by parasitic cohomology. -/
abbrev LiftedDerivedQCoh := ObjectProperty.verdierQuotient (liftedDerivedParasitic X)

/-- The canonical Verdier quotient functor, not a redefinition as `QC(X)`. -/
abbrev LiftedDerivedQCoh.quotientFunctor :
    LiftedDerivedLQCohFbc X ⥤ LiftedDerivedQCoh X :=
  ObjectProperty.verdierQuotientFunctor (liftedDerivedParasitic X)

end AlgebraicGeometry.AlgebraicStack
