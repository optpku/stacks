/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal-local detection of torsion-freeness

This leaf owns the domain criterion that torsion-freeness of a module can be checked after
localization at every maximal ideal.
-/

@[expose] public section

universe u v

namespace Module.IsTorsionFree

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a domain, torsion-freeness is equivalent to torsion-freeness of the canonical localized
module at every maximal ideal. -/
@[stacks 0AUT "maximal-local criterion for torsion-freeness"]
theorem iff_atPrime_maximal :
    IsTorsionFree R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        IsTorsionFree (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := sorry
-- Proof strategy: use `IsLocalizedModule.isTorsionFree` in the forward direction; for the reverse
-- direction apply `Module.IsTorsionFree.of_smul_eq_zero` and
-- `eq_zero_of_localization_maximal` to the canonical `LocalizedModule.mkLinearMap` maps.

end Module.IsTorsionFree
