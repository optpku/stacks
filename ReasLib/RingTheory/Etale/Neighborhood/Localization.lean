/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Etale.Neighborhood
public import ReasLib.RingTheory.Localization.AtPrime.ResidueField
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizations of etale neighborhoods

This leaf turns the bundled `PrimeSpectrum.EtaleNeighborhood` owner into the
prime-localization data used by henselization and stalk arguments.  The
relative localization algebra is deliberately named rather than registered
globally: Mathlib avoids a global `Algebra` instance here to prevent
localization diamonds.  The corresponding `CommAlgCat` object belongs to the
category bridge `CommAlgCat.Over.Etale.Neighborhood`, leaving this leaf at the
ring-theoretic layer.

@stack 04GV
-/

universe u v

namespace PrimeSpectrum.EtaleNeighborhood

/-- The canonical map from `Rₚ` to the localization of an etale neighborhood
at its selected point. -/
@[stacks 04GV "prime-localization map of an etale neighborhood"]
noncomputable abbrev localizationMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    Localization.AtPrime p.asIdeal →+*
      Localization.AtPrime U.point.asIdeal :=
  Localization.localRingHom p.asIdeal U.point.asIdeal
    (algebraMap R U.carrier) U.over

/-- The named `Rₚ`-algebra structure on `S_q` attached to an etale
neighborhood.  It is explicit because the corresponding Mathlib structure is
intentionally not a global instance. -/
@[stacks 04GV "relative prime-localization algebra of an etale neighborhood"]
noncomputable abbrev localizationAlgebra
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime U.point.asIdeal) := by
  letI : U.point.asIdeal.LiesOver p.asIdeal := ⟨U.over⟩
  exact Localization.AtPrime.algebraOfLiesOver p.asIdeal U.point.asIdeal

/-- The localization map sends a base generator to its image in the selected
localization. -/
@[simp, stacks 04GV "prime-localization map on base generators"]
theorem localizationMap_apply_algebraMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) (x : R) :
    U.localizationMap (algebraMap R (Localization.AtPrime p.asIdeal) x) =
      algebraMap U.carrier (Localization.AtPrime U.point.asIdeal)
        (algebraMap R U.carrier x) := sorry

/-- The maximal ideal of the selected localization contracts to the maximal
ideal of the base localization along the canonical localization map. -/
@[simp, stacks 04GV "locality of an etale-neighborhood localization map"]
theorem localizationMap_comap_maximalIdeal
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    Ideal.comap U.localizationMap
        (IsLocalRing.maximalIdeal (Localization.AtPrime U.point.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := sorry

/-- The residue-field map induced by the canonical localization map of an
etale neighborhood is bijective. -/
@[stacks 04GV "bijective residue-field map of an etale-neighborhood localization"]
theorem localizationMap_residueField_bijective
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    Function.Bijective
      (Ideal.ResidueField.map
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime U.point.asIdeal))
        U.localizationMap (localizationMap_comap_maximalIdeal U).symm) := sorry

/-- The residue-field equivalence induced by localizing an etale neighborhood
at its selected point. -/
@[stacks 04GV "residue-field equivalence after neighborhood localization"]
noncomputable def localizationResidueFieldEquiv
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).ResidueField ≃+*
      (IsLocalRing.maximalIdeal (Localization.AtPrime U.point.asIdeal)).ResidueField :=
  (Localization.AtPrime.residueFieldEquiv p.asIdeal).trans
    (U.residueFieldEquiv.trans
      (Localization.AtPrime.residueFieldEquiv U.point.asIdeal).symm)

/-- The underlying map of the localized residue-field equivalence is the
canonical residue-field map induced by `U.localizationMap`. -/
@[stacks 04GV "canonical map of a localized etale-neighborhood residue-field equivalence"]
theorem localizationResidueFieldEquiv_toRingHom
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    U.localizationResidueFieldEquiv.toRingHom =
      Ideal.ResidueField.map
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (IsLocalRing.maximalIdeal (Localization.AtPrime U.point.asIdeal))
        U.localizationMap (localizationMap_comap_maximalIdeal U).symm := sorry

/-- Pointwise formula for the residue-field equivalence induced by the
localized neighborhood. -/
@[simp, stacks 04GV "pointwise localized residue-field equivalence"]
theorem localizationResidueFieldEquiv_apply
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) (x : (IsLocalRing.maximalIdeal
      (Localization.AtPrime p.asIdeal)).ResidueField) :
    U.localizationResidueFieldEquiv x =
      (Localization.AtPrime.residueFieldEquiv U.point.asIdeal).symm
        (U.residueFieldEquiv (Localization.AtPrime.residueFieldEquiv p.asIdeal x)) := sorry

end PrimeSpectrum.EtaleNeighborhood
