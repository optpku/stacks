/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.Basic
public import ReasLib.RingTheory.GlobalDimension.Localization
public import ReasLib.RingTheory.GlobalDimension.ResidueField
public import ReasLib.RingTheory.RegularLocalRing.GlobalDimension

/-!
# Regular local rings and global dimension

This leaf owns the homological characterization of a Noetherian local regular
ring.  The residue-field projective dimension, finite global dimension, and
regular-local predicates are kept as their native owners; their equivalences
and dimension equalities are thin consequences of those owners.
-/

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The Krull dimension of a Noetherian local ring is bounded by the dimension
of its cotangent space over the residue field. -/
theorem ringKrullDim_le_finrank_cotangentSpace :
    ringKrullDim R ≤
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  simpa only [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] using
    ringKrullDim_le_spanFinrank_maximalIdeal R

end IsLocalRing

namespace IsFiniteGlobalDimensionRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A finite global-dimension bound makes the residue field have finite
projective dimension. -/
theorem residueField_projectiveDimension_ne_top
    [IsFiniteGlobalDimensionRing R] :
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤ := by
  obtain ⟨n, hn⟩ := IsFiniteGlobalDimensionRing.exists_bound (R := R)
  letI := hn
  exact (projectiveDimension_ne_top_iff _).mpr
    ⟨n, HasGlobalDimensionLE.hasProjectiveDimensionLE _⟩

/-- The cotangent-space dimension is bounded by the global dimension. -/
theorem finrank_cotangentSpace_le_globalDimension
    [IsFiniteGlobalDimensionRing R] :
    (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) ≤
      globalDimension R := by
  letI : HasGlobalDimensionLE R (globalDimension R) :=
    csInf_mem (IsFiniteGlobalDimensionRing.exists_bound (R := R))
  exact IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_residueField.trans
    ((projectiveDimension_le_iff _ _).mpr
      (HasGlobalDimensionLE.hasProjectiveDimensionLE _))

/-- For a Noetherian local ring of finite global dimension, global dimension
equals Krull dimension. -/
@[stacks 00OC "moreover, global dimension equals Krull dimension"]
theorem globalDimension_eq_ringKrullDim
    [IsFiniteGlobalDimensionRing R] :
    globalDimension R = ringKrullDim R := by
  have hle :
      (Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) ≤ ringKrullDim R :=
    IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_residueField.trans
      (IsLocalRing.projectiveDimension_residueField_le_ringKrullDim_of_ne_top
        residueField_projectiveDimension_ne_top)
  have hdim := le_antisymm IsLocalRing.ringKrullDim_le_finrank_cotangentSpace hle
  letI : IsRegularLocalRing R :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace R).mpr hdim.symm
  have hbound := IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim hdim
  have hglobal : globalDimension R ≤
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    csInf_le' hbound
  apply le_antisymm
  · show (globalDimension R : WithBot ℕ∞) ≤ ringKrullDim R
    rw [hdim]
    exact_mod_cast hglobal
  · show ringKrullDim R ≤ (globalDimension R : WithBot ℕ∞)
    exact IsLocalRing.ringKrullDim_le_finrank_cotangentSpace.trans
      finrank_cotangentSpace_le_globalDimension

/-- For a Noetherian local ring of finite global dimension, Krull dimension
equals cotangent-space dimension. -/
@[stacks 00OC "moreover, Krull dimension equals cotangent-space dimension"]
theorem ringKrullDim_eq_finrank_cotangentSpace
    [IsFiniteGlobalDimensionRing R] :
    ringKrullDim R =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  apply le_antisymm IsLocalRing.ringKrullDim_le_finrank_cotangentSpace
  rw [← globalDimension_eq_ringKrullDim]
  exact finrank_cotangentSpace_le_globalDimension

end IsFiniteGlobalDimensionRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Finite projective dimension of the residue field forces regularity of a
Noetherian local ring. -/
theorem of_residueField_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    IsRegularLocalRing R := by
  apply (iff_finrank_cotangentSpace R).mpr
  exact le_antisymm
    (IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_residueField.trans
      (IsLocalRing.projectiveDimension_residueField_le_ringKrullDim_of_ne_top hpd))
    IsLocalRing.ringKrullDim_le_finrank_cotangentSpace

/-- For a Noetherian local ring, the residue field has finite projective
dimension exactly when the ring has finite global dimension and is regular local. -/
@[stacks 00OC]
theorem residueField_projectiveDimension_tfae :
    List.TFAE
      [ projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤,
        IsFiniteGlobalDimensionRing R,
        IsRegularLocalRing R ] := by
  have hregular : IsRegularLocalRing R → IsFiniteGlobalDimensionRing R := by
    intro h
    letI := h
    exact ⟨⟨Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R),
      hasGlobalDimensionLE_of_ringKrullDim ((iff_finrank_cotangentSpace R).mp h).symm⟩⟩
  apply List.tfae_cons_cons.mpr
  constructor
  · show (projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) ↔
      IsFiniteGlobalDimensionRing R
    constructor
    · show (projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) →
        IsFiniteGlobalDimensionRing R
      exact fun h ↦ hregular (of_residueField_projectiveDimension_ne_top h)
    · show IsFiniteGlobalDimensionRing R →
        projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤
      intro h
      letI := h
      exact IsFiniteGlobalDimensionRing.residueField_projectiveDimension_ne_top
  · show List.TFAE [IsFiniteGlobalDimensionRing R, IsRegularLocalRing R]
    apply List.tfae_cons_cons.mpr
    constructor
    · show IsFiniteGlobalDimensionRing R ↔ IsRegularLocalRing R
      constructor
      · show IsFiniteGlobalDimensionRing R → IsRegularLocalRing R
        intro h
        letI := h
        exact of_residueField_projectiveDimension_ne_top
          IsFiniteGlobalDimensionRing.residueField_projectiveDimension_ne_top
      · show IsRegularLocalRing R → IsFiniteGlobalDimensionRing R
        exact hregular
    · show List.TFAE [IsRegularLocalRing R]
      exact List.tfae_singleton _

end IsRegularLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-- For a Noetherian local ring, regular-locality is equivalent to finite
global dimension. -/
@[stacks 0AFS "(1)"]
theorem iff_isFiniteGlobalDimensionRing [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ IsFiniteGlobalDimensionRing R :=
  (residueField_projectiveDimension_tfae (R := R)).out 2 1

/-- Regular-locality is preserved by localization at every prime. -/
@[stacks 0AFS "(2)"]
theorem localizationAtPrime [IsRegularLocalRing R] (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  letI : IsFiniteGlobalDimensionRing R := iff_isFiniteGlobalDimensionRing.mp inferInstance
  letI : IsFiniteGlobalDimensionRing (Localization.AtPrime p.asIdeal) :=
    IsFiniteGlobalDimensionRing.localization p.asIdeal.primeCompl
  exact iff_isFiniteGlobalDimensionRing.mpr inferInstance

end IsRegularLocalRing

namespace IsRegularRing

variable {R : Type u} [CommRing R]

/-- A regular local ring is regular after localization at every prime, packaged
as the canonical global regularity instance. -/
@[stacks 0AFS "(2), regular-local ring is regular"]
instance instOfIsRegularLocalRing [IsRegularLocalRing R] : IsRegularRing R := by
  apply isRegularRing_iff.mpr
  intro p hp
  exact IsRegularLocalRing.localizationAtPrime ⟨p, hp⟩

end IsRegularRing
