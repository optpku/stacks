/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite extensions of valuation rings

@stack 0ASH

The finite-extension consequences are separated from the valuation-ring
extension class so consumers that only need these invariants can import this
leaf directly.
-/

universe u v

open IsLocalRing IsExtensionOfValuationRings

namespace IsExtensionOfValuationRings

variable (A : Type u) (B : Type v)
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [CommRing B] [IsDomain B] [ValuationRing B]
variable [Algebra A B] [h : IsExtensionOfValuationRings A B]

-- Local instance justification (instance diamond): use the canonical fraction-field algebra only
-- while forming the finite-dimensional comparison; it is intentionally not exported globally.
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Lemma 15.124.2 (1): a finite extension of the fraction fields of valuation rings induces a
finite-dimensional extension of residue fields. -/
@[stacks 0ASH "finite residue-field extension"]
theorem finiteDimensional_residueField
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    FiniteDimensional (ResidueField A) (ResidueField B) := sorry
-- Proof strategy: lift a residue-field linearly independent family to `B` and
-- prove the lifts remain linearly independent over `FractionRing A` by the
-- valuation-minimum argument.  Bound its cardinality by the finite fraction-
-- field dimension and apply the finite-dimensional criterion.

-- Local instance justification (proof-local temporary data): expose the preceding residue-field
-- finiteness theorem to typeclass search only in this finite-extension leaf.
attribute [local instance] finiteDimensional_residueField

/-- Lemma 15.124.2 (2): the value-group index of a finite fraction-field extension is finite. -/
@[stacks 0ASH "finite value-group index"]
theorem ramificationIndex_ne_top
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    ramificationIndex A B ≠ ⊤ := sorry
-- Proof strategy: choose representatives of distinct value-group cosets and
-- combine them with a residue-field basis.  Their products are linearly
-- independent in `FractionRing B`, so finite fraction-field dimension forces
-- the quotient value group, hence its `ENat.card`, to be finite.

/-- Lemma 15.124.2: for a finite extension of valuation rings, the value-group index times the
residue degree is bounded by the fraction-field degree. -/
@[stacks 0ASH "Lemma 15.124.2, valuation-group index times residue degree"]
theorem ramificationIndex_mul_residueDegree_le_finrank
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank (FractionRing A) (FractionRing B) := sorry
-- Proof strategy: choose a residue-field basis and one target fraction for each
-- value-group quotient class.  Prove that all products of the two families are
-- linearly independent over `FractionRing A` by separating minimal valuations
-- and then reducing the leading slice modulo the maximal ideal.  Compare the
-- resulting cardinality with the ambient finrank.

end IsExtensionOfValuationRings
