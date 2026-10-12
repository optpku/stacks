/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely Generated Module Properties

This leaf supplements Mathlib's bundled finitely generated module category with the canonical
closure of its object property under isomorphisms.
-/

@[expose] public section

universe u v

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- Finitely generated bundled modules are closed under isomorphisms. -/
@[stacks 00JH "finite module isomorphism closure"]
instance isFG.isClosedUnderIsomorphisms :
    (isFG.{v} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- Local instance justification (proof-local temporary data): supply the explicit finite-module
    -- predicate evidence required by the instance-based equivalence theorem.
    letI : Module.Finite R X := hX
    exact Module.Finite.equiv e.toLinearEquiv

/-- The zero bundled module is finitely generated. -/
instance isFGContainsZero : (isFG.{v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, isZero_of_subsingleton _, Module.Finite.of_finite⟩

/-- A subsingleton bundled module is finitely generated. -/
@[stacks 00JH "subsingleton module is finite"]
theorem isFG_of_subsingleton (M : ModuleCat.{v} R) [Subsingleton M] :
    isFG.{v} R M := by
  -- Local instance justification (proof-local temporary data): install the finite-type evidence
  -- produced from subsingletonness for the canonical finite-module theorem.
  letI : Finite M := Finite.of_subsingleton
  exact Module.Finite.of_finite

end ModuleCat
