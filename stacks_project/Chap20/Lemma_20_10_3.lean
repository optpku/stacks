/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Augmentation
import StacksCheckRecall

@[expose] public section

/- Lemma 20.10.3 (Tag 01EL): for a ringed site, the free Čech chain complex represents the
cochain complex obtained by evaluating a presheaf module on the Čech intersections.  The
ringed-space open-cover case is the specialization of these generic owners; no second
chapter-local comparison object is needed. -/

open AlgebraicGeometry.RingedSpace.ModuleCech

@[stacks 01EL] #check @overFamily
@[stacks 01EL] #check @chain
@[stacks 01EL] #check @homFunctor
@[stacks 01EL] #check @additiveComplex
@[stacks 01EL] #check @comparisonIso

open SheafOfModules.RingedSite.Cech

@[stacks 01EL] #check @freeChain_degree
@[stacks 01EL] #check @degreeComparison
@[stacks 01EL] #check @homComparisonIso

end
