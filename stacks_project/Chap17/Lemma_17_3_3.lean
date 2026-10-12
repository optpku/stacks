/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Pullback.Exactness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- Lemma 17.3.3 (1): direct image of module sheaves along a morphism of ringed spaces preserves
all limits. -/
@[stacks 01AJ "(1)"]
#check
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits :
    PreservesLimits (RingedSpace.Hom.pushforward f))

/- The left exactness assertion in Lemma 17.3.3 (1) follows at the general adjunction layer. -/
#check
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).rightAdjoint_leftExact :
    leftExactFunctor X.Modules Y.Modules (RingedSpace.Hom.pushforward f))

/- Lemma 17.3.3 (2): inverse image of module sheaves along a morphism of ringed spaces preserves
all colimits. -/
@[stacks 01AJ "(2)"]
#check
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits :
    PreservesColimits (RingedSpace.Hom.pullback f))

/- The right exactness assertion in Lemma 17.3.3 (2) follows at the general adjunction layer. -/
#check
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).leftAdjoint_rightExact :
    rightExactFunctor Y.Modules X.Modules (RingedSpace.Hom.pullback f))

/- Lemma 17.3.3 (3): inverse image of abelian sheaves along the underlying continuous map of a
morphism of ringed spaces is exact. -/
@[stacks 01AJ "(3)"]
#check
  (TopCat.Sheaf.pullback_addCommGrp_exact f.hom.base :
    exactFunctor (Y.carrier.Sheaf AddCommGrpCat.{u}) (X.carrier.Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base))

end AlgebraicGeometry
