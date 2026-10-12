/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme
import StacksCheckRecall

open CategoryTheory Limits

universe u

section

variable {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)

/- 40.3.0.1: composition has the target of the later arrow. -/
@[stacks 04LF] #check
  (AlgebraicGeometry.GroupoidScheme.composition_target G :
    G.c ≫ G.t = pullback.fst G.s G.t ≫ G.t)

/- The projections from the composable-arrow pullback have matching source and target. -/
#check
  (CategoryTheory.Limits.pullback.condition :
    pullback.fst G.s G.t ≫ G.s = pullback.snd G.s G.t ≫ G.t)

/- Composition has the source of the earlier arrow. -/
#check
  (AlgebraicGeometry.GroupoidScheme.comp_source G :
    G.c ≫ G.s = pullback.snd G.s G.t ≫ G.s)

end
