/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Lemma 17.22.3 (0A6F): restriction of scalars is left adjoint to coextension of scalars.  The
shared owner registers the canonical right-adjoint existence fact, so no local instance or
explicit adjoint witness is required downstream. -/
@[stacks 0A6F]
#check @restrictionCoextendAdj

#check @coextendAlong
#check @restrictionAlong_isLeftAdjoint
