/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.FiberwiseColimit.LowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit

/- Lemma 21.38.8 (08PE): projection lower shriek on an inherited site is the sheafification of
the presheaf obtained by taking colimits over the fibers of the projection. -/
@[stacks 08PE "fiberwise-colimit presheaf"]
#check @functor

@[stacks 08PE "fiberwise-colimit object formula"]
#check @fiberwiseColimitObj

@[stacks 08PE "sheafified fiberwise-colimit functor"]
#check @sheafFunctor

@[stacks 08PE "fiberwise-colimit adjunction"]
#check @sheafAdjunction

@[stacks 08PE]
#check @lowerShriekIso

@[stacks 08PE "objectwise lower-shriek computation"]
#check @lowerShriekObjIso

end CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit
