/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Lattice.Distance.Properties
public import ReasLib.Algebra.Module.Lattice.Noetherian

/-!
# Length comparisons for lattices

@stack 02MF
-/

@[expose] public section

universe u v w

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

namespace Submodule.IsLattice

/-- Lemma 10.121.4 (1): an overmodule of a lattice is a lattice exactly when its quotient has
finite length, equivalently when the overmodule is finite over the base ring. -/
@[stacks 02MF "(1)"]
theorem tfae_of_le {M M' : Submodule R V} [Submodule.IsLattice K M]
    (hdim : ringKrullDim R = 1) (hMM' : M ≤ M') :
    List.TFAE
      [ Submodule.IsLattice K M'
      , Module.length R (M' ⧸ M.submoduleOf M') < ⊤
      , Module.Finite R M'
      ] := sorry

/-- Lemma 10.121.4 (2): a submodule of a lattice is a lattice exactly when the quotient has
finite length. -/
@[stacks 02MF "(2)"]
theorem iff_length_lt_top_of_le {M M' : Submodule R V} [Submodule.IsLattice K M]
    (hdim : ringKrullDim R = 1) (hM'M : M' ≤ M) :
    Submodule.IsLattice K M' ↔
      Module.length R (M ⧸ M'.submoduleOf M) < ⊤ := sorry

end Submodule.IsLattice

namespace Submodule

/-- Lemma 10.121.4 (4): quotient length is additive along a chain of lattices. -/
@[stacks 02MF "(4)"]
theorem length_quotient_eq_add_of_lattice_chain
    {M M' M'' : Submodule R V}
    [IsLattice K M] [IsLattice K M'] [IsLattice K M'']
    (hdim : ringKrullDim R = 1) (hMM' : M ≤ M') (hM'M'' : M' ≤ M'') :
    Module.length R (M'' ⧸ M.submoduleOf M'') =
      Module.length R (M' ⧸ M.submoduleOf M') +
        Module.length R (M'' ⧸ M'.submoduleOf M'') := sorry

/-- Lemma 10.121.4 (5): the length difference computed from the intersection equals the
corresponding difference computed from the sum. -/
@[stacks 02MF "(5), intersection and sum"]
theorem length_difference_inf_eq_length_difference_sup
    {M M' : Submodule R V} [IsLattice K M] [IsLattice K M']
    (hdim : ringKrullDim R = 1) :
    ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) =
      ((Module.length R (↥(M ⊔ M') ⧸ M'.submoduleOf (M ⊔ M'))).toNat : ℤ) -
        ((Module.length R (↥(M ⊔ M') ⧸ M.submoduleOf (M ⊔ M'))).toNat : ℤ) := sorry

/-- Lemma 10.121.4 (5): replacing the sum by a common upper lattice does not change the
difference of quotient lengths. -/
@[stacks 02MF "(5), upper lattice"]
theorem length_difference_sup_eq_length_difference_of_sup_le
    {M M' N' : Submodule R V}
    [IsLattice K M] [IsLattice K M'] [IsLattice K N']
    (hdim : ringKrullDim R = 1) (hsup : M ⊔ M' ≤ N') :
    ((Module.length R (↥(M ⊔ M') ⧸ M'.submoduleOf (M ⊔ M'))).toNat : ℤ) -
        ((Module.length R (↥(M ⊔ M') ⧸ M.submoduleOf (M ⊔ M'))).toNat : ℤ) =
      ((Module.length R (N' ⧸ M'.submoduleOf N')).toNat : ℤ) -
        ((Module.length R (N' ⧸ M.submoduleOf N')).toNat : ℤ) := sorry

end Submodule
