module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Module.Support.IdealPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Support of ideal-power torsion modules

This leaf identifies the elementwise ideal-power torsion predicate with the
support condition owned by the sibling `IdealPower` file.

@stack 0953
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.89.6 (0953): for a finitely generated ideal `I`, an `R`-module is
`I`-power torsion exactly when its support is contained in `V(I)`. -/
@[stacks 0953 "ideal-power torsion and support"]
theorem isIdealPowerTorsion_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    IsIdealPowerTorsion I M ↔ support R M ⊆ zeroLocus I := sorry
-- Proof strategy: apply the finite-module support criterion to every cyclic submodule.
-- The forward direction localizes an elementwise power-annihilation witness; the reverse
-- direction uses `hI` to obtain a uniform power on each cyclic submodule.

end Module
