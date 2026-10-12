/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue-field projective dimension

This leaf records the two complementary bounds used for a Noetherian local ring: the cotangent
space gives a lower bound for the residue-field projective dimension, while finite projective
dimension gives an upper bound by Krull dimension.  Koszul complexes, minimal resolutions, and
Buchsbaum--Eisenbud rank calculations remain proof infrastructure rather than public data.
-/

@[expose] public section

universe u

open CategoryTheory

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The residue-field projective dimension is at least the cotangent-space
dimension. -/
@[stacks 00OA]
theorem finrank_cotangentSpace_le_projectiveDimension_residueField :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      projectiveDimension (ModuleCat.of R (ResidueField R)) := sorry

/-- The residue field does not have projective dimension strictly below the dimension of the
cotangent space. -/
@[stacks 00OA "projective-dimension predicate form"]
theorem not_hasProjectiveDimensionLT_finrank_cotangentSpace :
    ¬ HasProjectiveDimensionLT
        (ModuleCat.of R (ResidueField R))
        (Module.finrank (ResidueField R) (CotangentSpace R)) := sorry

/-- If the residue field has projective dimension `n`, then `n` is bounded by
the Krull dimension of the ring. -/
@[stacks 00OB]
theorem projectiveDimension_residueField_le_ringKrullDim
    {n : ℕ} (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = n) :
    n ≤ ringKrullDim R := sorry

/-- Finite projective dimension of the residue field is bounded by the Krull dimension. -/
@[stacks 00OB "finite projective-dimension bridge"]
theorem projectiveDimension_residueField_le_ringKrullDim_of_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R := sorry

end IsLocalRing
