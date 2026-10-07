module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.Basic
public import ReasLib.RingTheory.GlobalDimension.Localization
public import ReasLib.RingTheory.GlobalDimension.ResidueField

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
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := sorry

end IsLocalRing

namespace IsFiniteGlobalDimensionRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A finite global-dimension bound makes the residue field have finite
projective dimension. -/
theorem residueField_projectiveDimension_ne_top
    [IsFiniteGlobalDimensionRing R] :
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤ := sorry

/-- The cotangent-space dimension is bounded by the global dimension. -/
theorem finrank_cotangentSpace_le_globalDimension
    [IsFiniteGlobalDimensionRing R] :
    (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) ≤
      globalDimension R := sorry

/-- For a Noetherian local ring of finite global dimension, global dimension
equals Krull dimension. -/
@[stacks 00OC "moreover, global dimension equals Krull dimension"]
theorem globalDimension_eq_ringKrullDim
    [IsFiniteGlobalDimensionRing R] :
    globalDimension R = ringKrullDim R := sorry

/-- For a Noetherian local ring of finite global dimension, Krull dimension
equals cotangent-space dimension. -/
@[stacks 00OC "moreover, Krull dimension equals cotangent-space dimension"]
theorem ringKrullDim_eq_finrank_cotangentSpace
    [IsFiniteGlobalDimensionRing R] :
    ringKrullDim R =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := sorry

end IsFiniteGlobalDimensionRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Finite projective dimension of the residue field forces regularity of a
Noetherian local ring. -/
theorem of_residueField_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    IsRegularLocalRing R := sorry

/-- For a Noetherian local ring, the residue field has finite projective
dimension exactly when the ring has finite global dimension and is regular local. -/
@[stacks 00OC]
theorem residueField_projectiveDimension_tfae :
    List.TFAE
      [ projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤,
        IsFiniteGlobalDimensionRing R,
        IsRegularLocalRing R ] := sorry

end IsRegularLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-- For a Noetherian local ring, regular-locality is equivalent to finite
global dimension. -/
@[stacks 0AFS "(1)"]
theorem iff_isFiniteGlobalDimensionRing [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ IsFiniteGlobalDimensionRing R := sorry

/-- Regular-locality is preserved by localization at every prime. -/
@[stacks 0AFS "(2)"]
theorem localizationAtPrime [IsRegularLocalRing R] (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := sorry

end IsRegularLocalRing

namespace IsRegularRing

variable {R : Type u} [CommRing R]

/-- A regular local ring is regular after localization at every prime, packaged
as the canonical global regularity instance. -/
@[stacks 0AFS "(2), regular-local ring is regular"]
instance instOfIsRegularLocalRing [IsRegularLocalRing R] : IsRegularRing R := sorry

end IsRegularRing
