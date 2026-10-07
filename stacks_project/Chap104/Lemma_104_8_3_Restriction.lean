module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Sites.Chaotic
public import stacks_project.Chap104.Lemma_104_5_3_Comparison
public import stacks_project.Chap96.Definition_96_26_1_QC

/-!
# Restriction of `D(𝒪_X)` to the chaotic affine site

An fppf `𝒪_X`-module restricts along `𝒳_affine ↪ 𝒳` to a module over the
chaotic affine structure sheaf, after the canonical `u → u+1` universe lift
of carriers and coefficients. The induced derived functor is the landing
map for the affine comparison of `Lg_!`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.AssociatedModule CategoryTheory
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The chaotic affine ringed site `(𝒳_affine, 𝒪)` of a category fibred in
groupoids. -/
abbrev affineChaoticRingedSite :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)

/-- `affineChaoticRingedSite X` is the commutative chaotic presentation of
`𝒳_affine`. -/
theorem affineChaoticRingedSite_eq :
    affineChaoticRingedSite X =
      RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X) :=
  sorry

/-- Restriction of an fppf `𝒪_X`-module along the affine inclusion, as a
presheaf of modules over the restricted structure sheaf. -/
def restrictToAffinePresheaf :
    fppfModules X ⥤
      PresheafOfModules ((affineInclusion X).op ⋙ (structureSheaf X).obj) :=
  SheafOfModules.forget (structureSheaf X) ⋙
    PresheafOfModules.pushforward₀ (affineInclusion X) (structureSheaf X).obj

/-- Objectwise, `restrictToAffinePresheaf` evaluates at an affine object `x` as
the fppf sections of the original module at `x.obj`. -/
theorem restrictToAffinePresheaf_obj (M : fppfModules X) (x : affineSite X) :
    ((restrictToAffinePresheaf X).obj M).obj (op x) =
      M.val.obj (op x.obj) :=
  sorry

/-- Restriction of fppf `𝒪_X`-modules to the chaotic affine site: precompose
along `affineInclusion`, universe-lift carriers and coefficients, and identify
the coefficient sheaf with `affineStructureSheaf`. -/
def restrictToAffineModules :
    fppfModules X ⥤ RingedSite.ModuleCat.{u + 1} (affineChaoticRingedSite X) where
  obj M :=
    ⟨liftedModulePresheaf (affineToOver X) ((restrictToAffinePresheaf X).obj M),
      Presheaf.isSheaf_bot _⟩
  map f :=
    ⟨liftedModuleNatTrans (affineToOver X) ((restrictToAffinePresheaf X).map f)⟩
  map_id := sorry
  map_comp := sorry

/-- Sections of `restrictToAffineModules` at an affine object `x` are the
universe-lifted fppf sections at `x.obj`. -/
theorem restrictToAffineModules_obj (M : fppfModules X) (x : affineSite X) :
    ((restrictToAffineModules X).obj M).val.obj (op x) =
      (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
        ((ModuleCat.uliftFunctor.{u + 1, u} _).obj (M.val.obj (op x.obj))) :=
  sorry

/-- The underlying module presheaf of `restrictToAffineModules` is the
universe lift of `restrictToAffinePresheaf`. -/
theorem restrictToAffineModules_val (M : fppfModules X) :
    ((restrictToAffineModules X).obj M).val =
      liftedModulePresheaf (affineToOver X) ((restrictToAffinePresheaf X).obj M) :=
  sorry

/-- Restriction of fppf modules to the chaotic affine site is additive. -/
instance restrictToAffineModules.instAdditive :
    (restrictToAffineModules X).Additive :=
  sorry

/-- Restriction of fppf modules to the chaotic affine site preserves finite
limits. -/
instance restrictToAffineModules.preservesFiniteLimits :
    PreservesFiniteLimits (restrictToAffineModules X) :=
  sorry

/-- Restriction of fppf modules to the chaotic affine site preserves finite
colimits. -/
instance restrictToAffineModules.preservesFiniteColimits :
    PreservesFiniteColimits (restrictToAffineModules X) :=
  sorry

/-- Bundled exact underived restriction of fppf modules to the chaotic affine
site. -/
abbrev restrictToAffineModules.exact :
    fppfModules X ⥤ₑ RingedSite.ModuleCat.{u + 1} (affineChaoticRingedSite X) :=
  ExactFunctor.of (restrictToAffineModules X)

/-- `restrictToAffineModules.exact` is `ExactFunctor.of` of underived affine
restriction. -/
theorem restrictToAffineModules.exact_eq :
    restrictToAffineModules.exact X = ExactFunctor.of (restrictToAffineModules X) :=
  sorry

/-- The standard derived-category structure on chaotic affine `𝒪`-modules. -/
abbrev affineChaoticHasDerivedCategory :
    HasDerivedCategory.{u + 2}
      (RingedSite.ModuleCat.{u + 1, u + 1, u, u + 1} (affineChaoticRingedSite X)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (affineChaoticRingedSite X)

/-- `affineChaoticHasDerivedCategory` is the standard derived-category
structure on chaotic affine modules. -/
theorem affineChaoticHasDerivedCategory_eq :
    affineChaoticHasDerivedCategory X =
      RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
        (affineChaoticRingedSite X) :=
  sorry

variable [AlgebraicStack X]

/-- Derived restriction `D(𝒪_X) ⥤ D(𝒳_affine, 𝒪)` of fppf module complexes to
the chaotic affine site. -/
def restrictToAffineDerived :
    ModuleDerived X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1, u + 1, u, u + 1}
        (affineChaoticRingedSite X) :=
  @Functor.mapDerivedCategory
    (fppfModules X) _ _ _
    (RingedSite.ModuleCat.{u + 1, u + 1, u, u + 1} (affineChaoticRingedSite X)) _ _
    (affineChaoticHasDerivedCategory X) (restrictToAffineModules X) _ _ _

/-- `restrictToAffineDerived` is `mapDerivedCategory` of underived affine
restriction, using the standard chaotic affine derived-category structure. -/
theorem restrictToAffineDerived_eq :
    restrictToAffineDerived X =
      @Functor.mapDerivedCategory
        (fppfModules X) _ _ _
        (RingedSite.ModuleCat.{u + 1, u + 1, u, u + 1} (affineChaoticRingedSite X))
        _ _ (affineChaoticHasDerivedCategory X)
        (restrictToAffineModules X) _ _ _ :=
  sorry

/-- The image of `Lg_! K` on the chaotic affine site, for
`K ∈ D_QCoh(𝒪_{X_flat,fppf})`. -/
abbrev restrictLowerShriekToAffine :
    DerivedQCohFlatFppf X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1, u + 1, u, u + 1}
        (affineChaoticRingedSite X) :=
  DerivedQCohFlatFppf.inclusion X ⋙
    derivedFlatFppfLowerShriek X ⋙ restrictToAffineDerived X

/-- Objectwise, `restrictLowerShriekToAffine` is derived affine restriction of
`Lg_!` applied to the flat-fppf quasi-coherent inclusion. -/
theorem restrictLowerShriekToAffine_obj (K : DerivedQCohFlatFppf X) :
    (restrictLowerShriekToAffine X).obj K =
      (restrictToAffineDerived X).obj
        ((derivedFlatFppfLowerShriek X).obj
          ((DerivedQCohFlatFppf.inclusion X).obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
