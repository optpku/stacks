/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
import StacksCheckRecall

/-!
# Quotients by ideal sheaves

The reusable owner constructs the sectionwise quotient presheaf explicitly and then applies
commutative-ring sheafification.  This file is a compatibility and discoverability facade.
-/

@[expose] public section

/- The quotient-sheaf comparison used in Lemma 18.28.16 (0GLY). -/
@[stacks 0GLY "quotient map"]
#check @SheafOfModules.RingedSite.IdealSheaf.TargetQuotient.ringMap

/- Source quotient objects and projections. -/
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.presheaf
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.sheaf
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.projection
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.ringSheaf
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.ringProjection

/- Quotients by ideal powers and the target-side quotient. -/
#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.sheaf
#check @SheafOfModules.RingedSite.IdealSheaf.PowerQuotient.projection
#check @SheafOfModules.RingedSite.IdealSheaf.TargetQuotient.sheaf
#check @SheafOfModules.RingedSite.IdealSheaf.TargetQuotient.projection

/- Uniform annihilation by an ideal power. -/
#check @SheafOfModules.RingedSite.IdealPower.IsAnnihilated
#check @SheafOfModules.RingedSite.IdealPower.isAnnihilated_iff
