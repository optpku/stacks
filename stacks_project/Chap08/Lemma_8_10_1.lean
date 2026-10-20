module

public import ReasLib.CategoryTheory.Fibered.InheritedPrecoverage.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.10.1

The lifted covering families are represented by `Precoverage.stronglyCartesianLift`. The lemma's
site conclusion is exposed by the four fine-grained precoverage instances recalled below.
-/

namespace CategoryTheory

/- The covering families are the strongly cartesian lifts of base covering families. -/
#check @Precoverage.stronglyCartesianLift
#check @Precoverage.StronglyCartesianLift.mem_iff
#check @Precoverage.StronglyCartesianLift.arrow_isStronglyCartesian
#check @Precoverage.StronglyCartesianLift.map_mem
#check @Precoverage.StronglyCartesianLift.ofArrows_mem_iff

/- Lemma 8.10.1 (1): the lifted precoverage contains isomorphisms. -/
@[stacks 06NU "(1) isomorphisms"]
#check @Precoverage.StronglyCartesianLift.hasIsos

/- Lemma 8.10.1 (2): lifted covering families are stable under composition. -/
@[stacks 06NU "(2) composition"]
#check @Precoverage.StronglyCartesianLift.isStableUnderComposition

/- Lemma 8.10.1 (3): lifted covers admit pullbacks along arbitrary morphisms. -/
@[stacks 06NU "(3) pullback existence"]
#check @Precoverage.StronglyCartesianLift.hasPullbacks

/- Lemma 8.10.1 (4): those pullback families are again lifted covers. -/
@[stacks 06NU "(4) base change"]
#check @Precoverage.StronglyCartesianLift.stableUnderBaseChange

/- Strongly cartesian arrows supply the reusable pullback constructions behind clause (4). -/
#check @Functor.IsStronglyCartesian.isPullback_of_base
#check @Functor.IsStronglyCartesian.isPullback_of_base_map
#check @Functor.IsStronglyCartesian.Pullback.isPullback
#check @Functor.IsStronglyCartesian.Pullback.fst.isStronglyCartesian
#check @Functor.IsPreFibered.PullbackMap.stronglyCartesian
#check @Functor.IsStronglyCartesian.hasPullback
#check @Functor.IsStronglyCartesian.fst_of_isPullback
#check @Functor.IsStronglyCartesian.map_isPullback

end CategoryTheory
