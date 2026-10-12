/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.4 (08TD): relative differentials are obtained by sheafifying the objectwise
presheaf of Kähler differentials. -/
@[stacks 08TD]
#check @SheafOfModules.RingedSite.relativeDifferentials_def

#check @TopCat.Sheaf.relativeDifferentials_def
