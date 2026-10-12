/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
public import ReasLib.RingTheory.Ideal.OfDefinition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Auto-associated rings

@stack 05GM

An auto-associated ring is a local commutative ring whose maximal ideal is weakly associated to
the regular module.
-/

@[expose] public section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R]

/-- Definition 15.15.1: a commutative ring is auto-associated when it is local and its maximal
ideal is weakly associated to its regular module. -/
@[stacks 05GM "Definition 15.15.1"]
class IsAutoAssociatedRing : Prop extends IsLocalRing R where
  /-- The maximal ideal is weakly associated to the regular module. -/
  maximalIdeal_weaklyAssociated :
    Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R)

variable {R}

/-- A local ring is auto-associated exactly when its maximal ideal is weakly associated to the
regular module. -/
@[stacks 05GM "auto-associated ring criterion"]
theorem isAutoAssociatedRing_iff [IsLocalRing R] :
    IsAutoAssociatedRing R ↔
      Ideal.IsWeaklyAssociatedToModule R R (maximalIdeal R) := sorry
-- Proof strategy: project `IsAutoAssociatedRing.maximalIdeal_weaklyAssociated` in the forward
-- direction; in the reverse direction assemble the Prop class from the ambient `IsLocalRing R`
-- instance and the supplied weak-association witness.

namespace IsAutoAssociatedRing

/-- An auto-associated ring has an element whose annihilator is an ideal of definition. -/
@[stacks 05GM "torsion ideal of definition"]
theorem exists_torsionOf_isIdealOfDefinition [IsAutoAssociatedRing R] :
    ∃ x : R, (Ideal.torsionOf R R x).IsIdealOfDefinition := sorry
-- Proof strategy: unpack weak association as a minimal-prime witness
-- `maximalIdeal R ∈ (Ideal.torsionOf R R x).minimalPrimes`; locality forces every minimal prime
-- of that torsion ideal to equal the maximal ideal.  Rewrite its radical as the infimum of its
-- minimal primes and apply `Ideal.isIdealOfDefinition_iff_isMaximal_radical`.

end IsAutoAssociatedRing

namespace IsAutoAssociatedRing

/-- Every field is auto-associated. -/
@[stacks 05GM "fields are auto-associated"]
instance of_field (K : Type u) [Field K] : IsAutoAssociatedRing K := sorry
-- Proof strategy: use the canonical local-ring instance for a field, rewrite its maximal ideal as
-- bottom, exhibit bottom as associated to the regular module via the element `1`, and pass from
-- associated to weakly associated with
-- `Ideal.IsAssociatedToModule.isWeaklyAssociatedToModule`.

end IsAutoAssociatedRing
