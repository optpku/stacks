/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
import StacksCheckRecall

/-!
# Lemma 17.18.2

The geometric implication is owned at the ringed-site level, while comparison with internal
Hom is the general closed-monoidal uniqueness-of-duals API.
-/

@[expose] public section

/- Lemma 17.18.2: a module sheaf admitting a specified left dual is locally a retract of a
finite free module sheaf. -/
@[stacks 0FNW "(1)"]
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.ofExactPairing

/- Lemma 17.18.2: a specified left dual is canonically isomorphic to the internal Hom into the
tensor unit. -/
@[stacks 0FNW "(2)"]
#check @CategoryTheory.ExactPairing.curryEvaluationIso

/- Lemma 17.18.2: uncurrying the canonical comparison recovers the specified evaluation. -/
@[stacks 0FNW "(3)"]
#check @CategoryTheory.ExactPairing.uncurry_curryEvaluationIso_hom

/- The ringed-site predicate has the expected point-neighborhood interpretation on ringed
spaces. -/
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.existsNeighborhood
