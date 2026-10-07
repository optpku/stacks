module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.BoundedAbove
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Limit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Above Limits of Ideal-Power Towers

Over a Noetherian ring, boundedness of the first stage propagates uniformly through a Cartesian
ideal-power tower.  This leaf owns boundedness of the limit and invertibility of its concrete
base-change map; the general propagation mechanism lives in `DerivedTower.BoundedAbove`.

@stack 09AU
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTower.BoundedAbove

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Lemma 15.98.5 (09AU), boundedness clause: a homotopy limit of the stated Cartesian
ideal-power tower is bounded above. -/
@[stacks 09AU "(1), bounded-above ideal-power limit"]
theorem limit [IsNoetherianRing A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsBoundedAbove)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) :
    K.IsBoundedAbove := sorry

namespace Limit

/-- Lemma 15.98.5 (09AU), base-change clause: the map from the presented limit after base change
to stage `n` is an isomorphism in every explicit derived extension model. -/
@[stacks 09AU "(3), bounded-above ideal-power limit base change"]
theorem baseChangeMap_isIso [IsNoetherianRing A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsBoundedAbove)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (P : HomotopyLimit.Presentation T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    IsIso (IdealPowerTower.Limit.baseChangeMap T P n E) := sorry

/-- Without choosing a homotopy-limit presentation publicly, base change of the intrinsic
bounded-above limit is nonemptily isomorphic to stage `n`. -/
@[stacks 09AU "presentation-independent bounded-above ideal-power base change"]
theorem nonemptyIso [IsNoetherianRing A]
    (T : IdealPowerTower I)
    (h_first : (T.obj 0).IsBoundedAbove)
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : HomotopyLimit.IsOf T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    Nonempty (IdealPowerTower.Limit.baseChange K n E ≅ T.obj n) := sorry

end Limit

end CategoryTheory.ModuleCat.IdealPowerTower.BoundedAbove
