/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Torsion killed by powers of a principal ideal

The canonical owner is `Ideal.primaryComponent`.  This file only gives the
small principal-ideal bridge used by ring constructions; it deliberately does
not introduce a second `powerTorsion` owner in the `Ideal` namespace.
-/

@[expose] public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- The ideal of elements annihilated by some power of `a`, expressed through
the canonical primary-component construction. -/
@[stacks 0BIP "principal power torsion"]
abbrev principalPowerTorsion (a : A) : Ideal A :=
  (Ideal.span ({a} : Set A)).primaryComponent A

/-- Membership in `principalPowerTorsion a` is annihilation by some power of `a`. -/
@[simp]
theorem mem_principalPowerTorsion_iff (a x : A) :
    x ∈ principalPowerTorsion a ↔ ∃ n : ℕ, a ^ n * x = 0 := sorry

end Ideal
