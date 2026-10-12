/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Retracts
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

@[expose] public section

/-!
# Retracts of perfect derived modules on ringed spaces

Perfectness on `D(𝒪_X)` inherits the generic ringed-site stability under retracts.  The theorems
below expose the direct-summand consequences without rebuilding localization or restriction data.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Lemma 20.49.9: if a binary biproduct of derived `𝒪_X`-modules is perfect, then both
summands are perfect. -/
@[stacks 08CS]
theorem isPerfect_summands_of_biprod
    (K L : ModuleDerived X)
    (hKL : IsPerfect (K ⊞ L)) :
    IsPerfect K ∧ IsPerfect L := sorry

/-- The left summand of a perfect binary biproduct in `D(𝒪_X)` is perfect. -/
theorem isPerfect_left_of_biprod
    (K L : ModuleDerived X)
    (hKL : IsPerfect (K ⊞ L)) :
    IsPerfect K := sorry

/-- The right summand of a perfect binary biproduct in `D(𝒪_X)` is perfect. -/
theorem isPerfect_right_of_biprod
    (K L : ModuleDerived X)
    (hKL : IsPerfect (K ⊞ L)) :
    IsPerfect L := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
