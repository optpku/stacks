module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Point.Skyscraper
public import ReasLib.Algebra.Module.TwistedFunction
import StacksCheckRecall

@[expose] public section

/- The canonical point-specific ring and module inverse/direct-image API. -/
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.inverseImageRing
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.unit
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.modulePullback
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.modulePushforward
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.moduleAdjunction

/- Lemma 18.37.2 (1): direct image on modules at a ringed-topos point is exact. -/
@[stacks 05V8 "(1)"]
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.modulePushforward_exact

/- Lemma 18.37.2 (2): the canonical counit is linear by construction and is epic. -/
@[stacks 05V8 "(2)"]
#check @CategoryTheory.GrothendieckTopology.Point.Ringed.moduleAdjunction_counit_epi

/- Lemma 18.37.2 (3): a nontrivial scalar action obstructs linearity of the additive
constant-function splitting. -/
@[stacks 05V8 "(3)"]
#check @TwistedFunction.not_exists_linearMap_eq_const
