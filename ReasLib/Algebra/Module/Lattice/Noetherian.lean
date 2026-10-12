/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lattices over Noetherian domains

This leaf extends Mathlib's `Submodule.IsLattice` API from principal ideal rings to Noetherian
domains.  The denominator-clearing lemmas need only a fraction field; Noetherianity enters only
when proving that the intersection of two lattices is finitely generated.
-/

@[expose] public section

open scoped Pointwise

universe u v w

namespace Submodule.IsLattice

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [Field K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Lemma 10.121.4 (Stacks `02MF`), denominator-clearing API: a finite submodule of a
fraction-field module can be scaled into a lattice by one nonzero element of the base domain. -/
@[stacks 02MF "common denominator"]
theorem exists_nonzero_smul_le {M N : Submodule R V}
    [IsDomain R] [IsFractionRing R K] [IsLattice K M] [Module.Finite R N] :
    ∃ a : R, a ≠ 0 ∧ a • N ≤ M := sorry

/-- Lemma 10.121.4 (Stacks `02MF`): scaling a lattice by a nonzero element of the base domain
again gives a lattice in the fraction-field module. -/
@[stacks 02MF "nonzero scalar multiple"]
theorem smul_of_ne_zero {M : Submodule R V}
    [IsDomain R] [IsFractionRing R K] [IsLattice K M] {a : R} (ha : a ≠ 0) :
    IsLattice K (a • M : Submodule R V) := sorry

/-- Lemma 10.121.4 (3) (Stacks `02MF`): over a Noetherian domain, the intersection of two
lattices in a fraction-field module is again a lattice. -/
@[stacks 02MF "(3), intersection"]
instance (priority := 900) inf_of_isNoetherianRing
    [IsDomain R] [IsFractionRing R K] [IsNoetherianRing R]
    (M N : Submodule R V) [IsLattice K M] [IsLattice K N] :
    IsLattice K (M ⊓ N) := sorry

end Submodule.IsLattice
