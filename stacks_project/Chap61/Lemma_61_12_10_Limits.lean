module

public import stacks_project.Chap61.Definition_61_12_8_Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Limits in chosen pro-étale sites

This file records pullback, equalizer, and terminal-object properties of a
chosen big pro-étale presentation and of its slice, small, and big-affine
carriers. Carrier equalizers and a final object agreeing with `Spec (ULift ℤ)`
are stated relative to an explicit represented terminal scheme; they are not
properties of an arbitrary pullback-closed presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable (X : ChosenBigProetaleSite.{u, v})

/-- The carrier of a chosen big pro-étale presentation has pullbacks. -/
theorem carrierHasPullbacks : HasPullbacks X.carrier :=
  X.hasPullbacks

/-- The unique morphism in a chosen big pro-étale carrier to a represented
`Spec (ULift ℤ)`. -/
noncomputable def carrierFrom (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (Y : X.carrier) : Y ⟶ Z :=
  X.fullyFaithful.preimage (specULiftZIsTerminal.from (X.toScheme.obj Y) ≫ e.inv)

/-- Every morphism in a chosen big pro-étale carrier to a represented
`Spec (ULift ℤ)` is the canonical one. -/
theorem carrierFrom_unique (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (Y : X.carrier) (f : Y ⟶ Z) :
    f = carrierFrom X Z e Y := sorry

/-- A represented `Spec (ULift ℤ)` is terminal in a chosen big pro-étale
carrier. -/
noncomputable def carrierIsTerminal (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    IsTerminal Z :=
  IsTerminal.ofUniqueHom (carrierFrom X Z e) (carrierFrom_unique X Z e)

/-- A chosen big pro-étale carrier containing a represented `Spec (ULift ℤ)`
has a terminal object. -/
theorem carrierHasTerminal (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasTerminal X.carrier :=
  (carrierIsTerminal X Z e).hasTerminal

/-- A chosen big pro-étale carrier containing a represented `Spec (ULift ℤ)`
has binary products, constructed as pullbacks over that object. -/
theorem carrierHasBinaryProducts (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasBinaryProducts X.carrier :=
  @hasBinaryProducts_of_hasTerminal_and_pullbacks X.carrier _
    (carrierHasTerminal X Z e) X.hasPullbacks

/-- A chosen big pro-étale carrier containing a represented `Spec (ULift ℤ)`
has equalizers, constructed from pullbacks and binary products over that
object. -/
theorem carrierHasEqualizers (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasEqualizers X.carrier :=
  @hasEqualizers_of_hasPullbacks_and_binary_products X.carrier _
    (carrierHasBinaryProducts X Z e) X.hasPullbacks

/-- The source-scheme functor preserves the empty limit as soon as the chosen
carrier contains a represented `Spec (ULift ℤ)`. -/
theorem toSchemePreservesTerminal (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    PreservesLimitsOfShape (Discrete.{0} PEmpty) X.toScheme :=
  @preservesLimitsOfShape_pempty_of_preservesTerminal _ _ _ _ X.toScheme
    (preservesLimit_of_preserves_limit_cone (carrierIsTerminal X Z e)
      ((isLimitMapConeEmptyConeEquiv X.toScheme Z).symm
        (IsTerminal.ofIso specULiftZIsTerminal e.symm)))

/-- The source-scheme functor preserves equalizers as soon as the chosen
carrier contains a represented `Spec (ULift ℤ)`. -/
theorem toSchemePreservesEqualizers (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    PreservesLimitsOfShape WalkingParallelPair X.toScheme :=
  @preservesEqualizers_of_preservesPullbacks_and_binaryProducts
    X.carrier _ _ _ X.toScheme (carrierHasBinaryProducts X Z e) X.hasPullbacks
    (@preservesBinaryProducts_of_preservesTerminal_and_pullbacks
      _ _ _ _ X.toScheme (carrierHasTerminal X Z e) X.hasPullbacks
      (toSchemePreservesTerminal X Z e)
      (ChosenBigSite.toSchemePreservesPullbacks X))
    (ChosenBigSite.toSchemePreservesPullbacks X)

variable (S : X.carrier)

/-- Weakly étale objects of a chosen big pro-étale slice are closed under
pullbacks. -/
theorem smallObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallObjects X S) WalkingCospan := sorry

/-- The canonical chosen small pro-étale carrier has pullbacks. -/
theorem smallSiteHasPullbacks : HasPullbacks (smallSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small pro-étale
carrier preserves pullbacks. -/
theorem smallToSchemePreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallToScheme X S) := sorry

/-- Affine-source objects of the canonical chosen big pro-étale slice are
closed under pullbacks. -/
theorem bigAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (bigAffineObjects X S) WalkingCospan := sorry

/-- The canonical chosen big affine pro-étale carrier has pullbacks. -/
theorem bigAffineSiteHasPullbacks : HasPullbacks (bigAffineSite X S) := sorry

/-- The source-scheme functor from the canonical chosen big affine pro-étale
carrier preserves pullbacks. -/
theorem bigAffineToSchemePreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (bigAffineToScheme X S) := sorry

/-- The identity object `S/S` is terminal in the canonical chosen big
pro-étale slice. -/
noncomputable def bigSiteIdentityTerminal :
    IsTerminal (Over.mk (𝟙 S) : bigSite X S) :=
  Over.mkIdTerminal

/-- The chosen big pro-étale slice over `S` has equalizers, constructed from
slice pullbacks and the terminal object `S/S`. -/
theorem bigSiteHasEqualizers : HasEqualizers (bigSite X S) :=
  @hasEqualizers_of_hasPullbacks_and_binary_products (bigSite X S) _
    (@hasBinaryProducts_of_hasTerminal_and_pullbacks (bigSite X S) _
      (bigSiteIdentityTerminal X S).hasTerminal
      (ChosenBigSite.sliceHasPullbacks X S))
    (ChosenBigSite.sliceHasPullbacks X S)

/-- The source-scheme functor from a chosen big pro-étale slice preserves
equalizers. -/
theorem bigToSchemePreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (bigToScheme X S) := sorry

/-- Weakly étale objects of a chosen big pro-étale slice are closed under
equalizers. -/
theorem smallObjectsIsClosedUnderEqualizers :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallObjects X S) WalkingParallelPair := sorry

/-- The canonical chosen small pro-étale carrier has equalizers. -/
theorem smallSiteHasEqualizers : HasEqualizers (smallSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small pro-étale
carrier preserves equalizers. -/
theorem smallToSchemePreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (smallToScheme X S) := sorry

/-- The identity object `S/S` satisfies the small-site weakly étale
predicate. -/
theorem smallObjects_mk_id : smallObjects X S (Over.mk (𝟙 S)) :=
  ((X.toScheme.map_id S).symm ▸
    MorphismProperty.id_mem (@WeaklyEtale) (X.toScheme.obj S) :
      WeaklyEtale (X.toScheme.map (𝟙 S)))

/-- The identity object `S/S` as an object of the canonical chosen small
pro-étale carrier. -/
def smallTerminalObject : smallSite X S :=
  ⟨Over.mk (𝟙 S), smallObjects_mk_id X S⟩

/-- The canonical morphism from a chosen small pro-étale object to `S/S`. -/
def smallTerminalFrom (U : smallSite X S) :
    U ⟶ smallTerminalObject X S :=
  ObjectProperty.homMk (Over.homMk U.obj.hom (Category.comp_id _))

/-- Every morphism from a chosen small pro-étale object to `S/S` is the
canonical one. -/
theorem smallTerminalFrom_unique (U : smallSite X S)
    (f : U ⟶ smallTerminalObject X S) :
    f = smallTerminalFrom X S U := sorry

/-- The identity object `S/S` is terminal in the canonical chosen small
pro-étale carrier. -/
noncomputable def smallTerminalObjectIsTerminal :
    IsTerminal (smallTerminalObject X S) :=
  IsTerminal.ofUniqueHom (smallTerminalFrom X S) (smallTerminalFrom_unique X S)

end AlgebraicGeometry.ChosenBigProetaleSite
