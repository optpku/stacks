/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.LocalRing.Defs
public import ReasLib.Algebra.Module.Lattice.Distance
public import ReasLib.RingTheory.KrullDimension.LocalRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic properties of lattice distance

The definition lives in `Distance`.  This leaf keeps the algebraic laws and the one-dimensional
lattice additivity criterion separate, so users that only need the invariant do not import the
local-domain hypotheses.
-/

@[expose] public section

universe u v w

namespace Submodule

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The distance from a submodule to itself is zero. -/
@[stacks 02MH "self distance"]
theorem latticeDistance_self (M : Submodule R V) :
    latticeDistance M M = 0 := sorry

/-- Swapping the arguments negates the distance. -/
@[stacks 02MH "skew-symmetry"]
theorem latticeDistance_neg_swap (M M' : Submodule R V) :
    latticeDistance M M' = -latticeDistance M' M := sorry

end Submodule

namespace Submodule

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- In the field case, all `K`-lattices are the ambient submodule, so their distance vanishes. -/
@[stacks 02MH "field degeneracy"]
theorem latticeDistance_eq_zero_of_isField
    (M M' : Submodule R V) [IsLattice K M] [IsLattice K M']
    (hfield : IsField R) : latticeDistance M M' = 0 := sorry

end Submodule

namespace Submodule

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Lemma 10.121.4 (Stacks `02MF`): changing the common lower lattice does not change the
integer difference of the two quotient lengths. -/
@[stacks 02MF]
theorem length_difference_inf_eq_length_difference_of_le_inf
    {M M' N : Submodule R V}
    [IsLattice K M] [IsLattice K M'] [IsLattice K N]
    (hdim : ringKrullDim R = 1) (hNle : N ≤ M ⊓ M') :
    ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) =
      ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) := sorry

/-- Lemma 10.121.6 (Stacks `02MH`): distance is additive on three `K`-lattices over a
one-dimensional Noetherian local domain. -/
@[stacks 02MH]
theorem latticeDistance_add
    (M M' M'' : Submodule R V)
    [IsLattice K M] [IsLattice K M'] [IsLattice K M''] :
    latticeDistance M M'' = latticeDistance M M' + latticeDistance M' M'' := sorry

end Submodule
