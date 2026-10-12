/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat local extensions realizing residue-field extensions

This leaf owns the flat local-algebra producer attached to a field extension
of the residue field of a local ring.  Its conclusion retains the constructed
ring and all comparison data needed by downstream consumers.
-/

@[expose] public section

universe u v

namespace IsLocalRing.ResidueField

/-- Every field extension of the residue field of a local ring is realized by
a flat local algebra whose maximal ideal is extended from the base. -/
@[stacks 03C3 "flat local extension realizing a residue field"]
theorem exists_flat_localExtension
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K] [Algebra (IsLocalRing.ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R] K),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal R' := sorry

/-- Every finite-dimensional field extension of the residue field of a local ring
is realized by a flat local algebra whose maximal ideal is extended from the base. -/
theorem exists_flat_localExtension_of_finiteDimensional
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R] K),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal R' := by
  exact exists_flat_localExtension K

end IsLocalRing.ResidueField
