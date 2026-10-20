module

public import ReasLib.CategoryTheory.Linear.PrincipalPower.ModuleCat
import StacksCheckRecall

/-!
# Remark 15.94.7 (0H33)

The concrete quotient and torsion systems and their reusable Mittag-Leffler criterion are owned by
`ReasLib.CategoryTheory.Linear.PrincipalPower.ModuleCat`.

@stack 0H33
-/

@[expose] public section

/- Remark 15.94.7 (0H33): in the principal-power short exact tower, the middle cohomology
system is Mittag-Leffler exactly when the right principal-torsion system is Mittag-Leffler. -/
@[stacks 0H33]
#check @CategoryTheory.ModuleCat.PrincipalPower.shortExact_middle_isMittagLeffler_iff_torsion

#check @CategoryTheory.ModuleCat.PrincipalPower.quotientSystem
#check @CategoryTheory.ModuleCat.PrincipalPower.torsionSystem
#check @CategoryTheory.ModuleCat.PrincipalPower.tateModule
#check @CategoryTheory.ModuleCat.PrincipalPower.quotientSystem_isMittagLeffler
