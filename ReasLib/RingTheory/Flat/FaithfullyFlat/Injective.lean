/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace Module.FaithfullyFlat

/-- A faithfully flat commutative algebra over `ℤ` is not injective as a `ℤ`-module. -/
@[stacks 08XF]
theorem not_injective_int (T : Type u) [CommRing T] [Module.FaithfullyFlat ℤ T] :
    ¬ Module.Injective ℤ T := sorry

end Module.FaithfullyFlat
