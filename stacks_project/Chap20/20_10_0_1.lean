/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Presheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- 20.10.0.1 (01EI): for a ringed site, an indexed family in `Over U` defines the
module-valued Čech cochain-complex functor.  The generic owner keeps the scalar restriction and
the coefficient-free Čech construction at their canonical abstraction levels. -/
@[stacks 01EI "20.10.0.1: generic ringed-site Cech complex"]
#check @SheafOfModules.RingedSite.cechComplex

#check @SheafOfModules.RingedSite.sectionsOnOver
#check @SheafOfModules.RingedSite.cechCohomology

/- The opens-site specialization retains the source domain of presheaf modules on a ringed
space, rather than silently switching to sheaf modules. -/
@[stacks 01EI "20.10.0.1: ringed-space presheaf specialization"]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Presheaf.complex

#check @AlgebraicGeometry.RingedSpace.ModuleCech.Presheaf.sections
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Presheaf.cohomology

end
