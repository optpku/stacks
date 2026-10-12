/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Limit
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Perfect
import ReasLib.Algebra.Category.CommRingCat.IdealPower.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect Limits of Ideal-Power Towers

This file gives the perfect analogue of the pseudo-coherent ideal-power limit API.  Generic
stagewise propagation lives in `DerivedTower.Perfect`; derived completeness remains independent
of perfectness in the sibling `Completeness` leaf.

@stack 09AW
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTower.Perfect

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Lemma 15.98.4 (09AW), perfectness clause: the homotopy limit of a Cartesian ideal-power
tower with perfect first stage is perfect. -/
@[stacks 09AW "(1), perfect ideal-power limit"]
theorem limit [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPerfect)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) :
    K.IsPerfect := sorry

namespace Limit

/-- Lemma 15.98.4 (09AW), base-change clause: the map from the presented limit after base change
to stage `n` is an isomorphism in every explicit derived extension model. -/
@[stacks 09AW "(3), perfect ideal-power limit base change"]
theorem baseChangeMap_isIso [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPerfect)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (P : HomotopyLimit.Presentation T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    IsIso (IdealPowerTower.Limit.baseChangeMap T P n E) := sorry

/-- Without choosing a homotopy-limit presentation publicly, base change of the intrinsic
perfect limit is nonemptily isomorphic to stage `n`. -/
@[stacks 09AW "presentation-independent perfect ideal-power base change"]
theorem nonemptyIso [IsAdicComplete I A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsPerfect)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    Nonempty (IdealPowerTower.Limit.baseChange K n E ≅ T.obj n) := sorry

end Limit

end CategoryTheory.ModuleCat.IdealPowerTower.Perfect
