/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

@[expose] public section

/-!
# Cohomological boundedness of perfect derived modules

On a quasi-compact ringed space, local strict-perfect models admit uniform global lower and upper
bounds.  This leaf records the resulting canonical t-structure API independently of compactness.
-/

open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}} [CompactSpace X.carrier]

/-- On a quasi-compact ringed space, a perfect derived module is cohomologically bounded. -/
@[stacks 09J7 "perfect objects are bounded"]
theorem IsPerfect.bounded {K : ModuleDerived X} (hK : IsPerfect K) :
    (t.bounded : ObjectProperty (ModuleDerived X)) K := sorry

/-- On a quasi-compact ringed space, a perfect derived module is bounded above. -/
theorem IsPerfect.boundedAbove {K : ModuleDerived X} (hK : IsPerfect K) :
    (t.minus : ObjectProperty (ModuleDerived X)) K := sorry

/-- On a quasi-compact ringed space, a perfect derived module is bounded below. -/
theorem IsPerfect.boundedBelow {K : ModuleDerived X} (hK : IsPerfect K) :
    (t.plus : ObjectProperty (ModuleDerived X)) K := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
