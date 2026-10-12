/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.HomotopyLimit
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Limit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Completeness of Ideal-Power Tower Limits

Each quotient stage `A ⧸ I ^ (n + 1)` is annihilated by `I ^ (n + 1)` after restriction to
`A`.  Consequently every homotopy limit of the fixed-base tower is derived complete, without
Noetherian, Cartesian, finiteness, or adic-completeness assumptions.
@stack 091W
@stack 09AU
@stack 09AV
@stack 09AW
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTower

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- At stage `n`, every `f ∈ I` acts nilpotently after restriction to `A`; exponent `n + 1`
already suffices. -/
@[stacks 09AU "power annihilation on an ideal-power quotient stage"]
theorem pow_smul_id_toBase_eq_zero (T : IdealPowerTower I)
    {f : A} (hf : f ∈ I) (n : ℕ) :
    (f ^ (n + 1) : A) • 𝟙 (T.toBase.obj (Opposite.op n)) = 0 := sorry

/-- The ideal acts nilpotently on every fixed-base stage of an ideal-power derived tower. -/
@[stacks 091W "nilpotent ideal action on an ideal-power quotient stage"]
theorem toBase_isNilpotentOn (T : IdealPowerTower I) (n : ℕ) :
    I.IsNilpotentOn (T.toBase.obj (Opposite.op n)) := sorry

/-- The fixed-base tower underlying an ideal-power derived tower is power torsion. -/
@[stacks 091W "ideal-power towers are power torsion"]
theorem toBase_isPowerTorsion (T : IdealPowerTower I) :
    T.toBase.IsPowerTorsion I := sorry

/-- Every homotopy limit of an ideal-power derived tower is derived complete with respect to the
ideal. -/
@[stacks 09AV "derived-complete ideal-power homotopy limit",
  stacks 09AW "derived-complete ideal-power homotopy limit",
  stacks 09AU "derived-complete ideal-power homotopy limit"]
theorem limit_isDerivedComplete (T : IdealPowerTower I)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) :
    K.IsDerivedCompleteWithRespectTo I := sorry

end CategoryTheory.ModuleCat.IdealPowerTower
