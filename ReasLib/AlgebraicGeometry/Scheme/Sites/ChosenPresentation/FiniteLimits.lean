/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Finite limits in chosen big-site presentations containing Spec ℤ

A represented terminal scheme gives a terminal object, binary products, and
equalizers in a chosen big-site carrier, preserved by its scheme functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ChosenBigSite

/-- A chosen big-site presentation together with a represented copy of `Spec (ULift ℤ)`. -/
structure WithSpecZ (P : Precoverage Scheme.{u}) extends ChosenBigSite.{u, v} P where
  /-- The carrier object representing the spectrum of the integers. -/
  specZ : carrier
  /-- The represented scheme is isomorphic to the spectrum of the integers. -/
  specZIso : toScheme.obj specZ ≅ Spec (CommRingCat.of (ULift.{u} ℤ))

variable {P : Precoverage Scheme.{u}} (X : ChosenBigSite.{u, v} P)

/-- The unique morphism in a chosen big-site carrier to a represented
`Spec (ULift ℤ)`. -/
noncomputable def carrierFrom (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (Y : X.carrier) : Y ⟶ Z :=
  X.fullyFaithful.preimage (specULiftZIsTerminal.from (X.toScheme.obj Y) ≫ e.inv)

/-- Every morphism in a chosen big-site carrier to a represented
`Spec (ULift ℤ)` is the canonical one. -/
theorem carrierFrom_unique (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (Y : X.carrier) (f : Y ⟶ Z) :
    f = carrierFrom X Z e Y := by
  apply X.fullyFaithful.map_injective
  apply (cancel_mono e.hom).1
  exact specULiftZIsTerminal.hom_ext _ _

/-- A represented `Spec (ULift ℤ)` is terminal in a chosen big-site
carrier. -/
noncomputable def carrierIsTerminal (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    IsTerminal Z :=
  IsTerminal.ofUniqueHom (carrierFrom X Z e) (carrierFrom_unique X Z e)

/-- A chosen big-site carrier containing a represented `Spec (ULift ℤ)`
has a terminal object. -/
theorem carrierHasTerminal (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasTerminal X.carrier :=
  (carrierIsTerminal X Z e).hasTerminal

/-- A chosen big-site carrier containing a represented `Spec (ULift ℤ)`
has binary products, constructed as pullbacks over that object. -/
theorem carrierHasBinaryProducts (Z : X.carrier)
    (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasBinaryProducts X.carrier :=
  @hasBinaryProducts_of_hasTerminal_and_pullbacks X.carrier _
    (carrierHasTerminal X Z e) X.hasPullbacks

/-- A chosen big-site carrier containing a represented `Spec (ULift ℤ)`
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
      (toSchemePreservesPullbacks X))
    (toSchemePreservesPullbacks X)

/-- The canonical morphism from any carrier object to the represented spectrum
of the integers. -/
noncomputable def WithSpecZ.toSpecZ (X : WithSpecZ.{u, v} P)
    (Y : X.toChosenBigSite.carrier) : Y ⟶ X.specZ :=
  carrierFrom X.toChosenBigSite X.specZ X.specZIso Y


/-- Under the represented integer-spectrum isomorphism, `toSpecZ` is the
canonical scheme morphism to the actual integer spectrum. -/
@[simp]
theorem WithSpecZ.toSpecZ_map (X : WithSpecZ.{u, v} P)
    (Y : X.toChosenBigSite.carrier) :
    X.toScheme.map (X.toSpecZ Y) ≫ X.specZIso.hom =
      specULiftZIsTerminal.from (X.toScheme.obj Y) :=
  specULiftZIsTerminal.hom_ext _ _

end AlgebraicGeometry.ChosenBigSite
