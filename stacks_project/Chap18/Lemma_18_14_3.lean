/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (f : X.Hom Y)
variable [f.modulePushforward.{z}.IsRightAdjoint]

/- Lemma 18.14.3 (03DC) (1): module direct image is left exact. -/
section

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]

@[stacks 03DC "(1)"]
#check ((leftExactFunctor_iff f.modulePushforward.{z}).mpr inferInstance :
  leftExactFunctor _ _ f.modulePushforward.{z})

end

/- Lemma 18.14.3 (03DC) (2): module direct image preserves all limits. -/
@[stacks 03DC "(2)"]
#check (inferInstance : PreservesLimits f.modulePushforward.{z})

/- Lemma 18.14.3 (03DC) (3): module inverse image is right exact. -/
section

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]

@[stacks 03DC "(3)"]
#check ((rightExactFunctor_iff f.modulePullback.{z}).mpr inferInstance :
  rightExactFunctor _ _ f.modulePullback.{z})

end

/- Lemma 18.14.3 (03DC) (4): module inverse image preserves all colimits. -/
@[stacks 03DC "(4)"]
#check (inferInstance : PreservesColimits f.modulePullback.{z})

end RingedSite.Hom
