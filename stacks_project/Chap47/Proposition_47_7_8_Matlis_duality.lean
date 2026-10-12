/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.MatlisDuality.Duality
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace LinearMap.IsInjectiveHull

variable (R E : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull)

/- Proposition 47.7.8 (Matlis duality) -/
@[stacks 08Z9] #check
  (LinearMap.IsInjectiveHull.artinianDualIsEquivalence R E hι :
    Functor.IsEquivalence (LinearMap.IsInjectiveHull.artinianDual R E hι))

#check
  (LinearMap.IsInjectiveHull.noetherianDualIsEquivalence R E hι :
    Functor.IsEquivalence (LinearMap.IsInjectiveHull.noetherianDual R E hι))

#check
  (LinearMap.IsInjectiveHull.artinianEvaluationIsIso R E hι :
    IsIso (LinearMap.IsInjectiveHull.artinianEvaluation R E hι))

#check
  (LinearMap.IsInjectiveHull.noetherianEvaluationIsIso R E hι :
    IsIso (LinearMap.IsInjectiveHull.noetherianEvaluation R E hι))

end LinearMap.IsInjectiveHull
