/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Derivation.Regular

/-!
# Regular Elements Detected by Kahler Differentials

These are the universal-derivation corollaries of the generic derivation
criteria in `ReasLib.RingTheory.Derivation.Regular`.

@stack 00TW
-/

@[expose] public section

open scoped TensorProduct

namespace KaehlerDifferential

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra ℚ S]

/-- Lemma 10.140.6, tag `00TW`: if an `S`-linear functional takes `D R S f` to one, then `f` is
not nilpotent. -/
@[stacks 00TW "Kahler differential detects non-nilpotence"]
theorem not_isNilpotent_of_exists_linearMap_D_eq_one
    [Nontrivial S] (f : S)
    (hdf : ∃ theta : Ω[S⁄R] →ₗ[S] S, theta (D R S f) = 1) :
    ¬ IsNilpotent f := by
  obtain ⟨theta, htheta⟩ := hdf
  exact Derivation.not_isNilpotent_of_apply_eq_one
    (theta.compDer (D R S)) f (by simpa using htheta)

/-- Lemma 10.140.6, tag `00TW`: if an `S`-linear functional takes `D R S f` to one, then `f` is
regular in a Noetherian local algebra. -/
@[stacks 00TW "Kahler differential detects regular elements"]
theorem isRegular_of_exists_linearMap_D_eq_one
    [IsLocalRing S] [IsNoetherianRing S] (f : S)
    (hdf : ∃ theta : Ω[S⁄R] →ₗ[S] S, theta (D R S f) = 1) :
    IsRegular f := by
  obtain ⟨theta, htheta⟩ := hdf
  exact Derivation.isRegular_of_apply_eq_one
    (theta.compDer (D R S)) f (by simpa using htheta)

end KaehlerDifferential
