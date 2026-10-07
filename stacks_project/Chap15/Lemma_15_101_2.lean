module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.PseudoCoherent

@[expose] public section

/-!
# Lemma 15.101.2

@stack 0EGV
-/

/- Lemma 15.101.2 (1) (0EGV): the cohomology systems of the ideal-power derived tensor tower of a
pseudo-coherent object satisfy Mittag-Leffler. -/
@[stacks 0EGV "pseudo-coherent ideal-power tensor cohomology is Mittag-Leffler"]
#check @CategoryTheory.DerivedCategory.IdealPower.HomologySystem.isMittagLeffler_of_isPseudoCoherent

/- Lemma 15.101.2 (2) (0EGV): the quotient cohomology limit agrees with the limit of the
cohomology of the ideal-power derived tensor tower. -/
@[stacks 0EGV "pseudo-coherent ideal-power quotient cohomology limit"]
#check @CategoryTheory.DerivedCategory.IdealPower.HomologySystem.quotientLimit_of_isPseudoCoherent

#check @CategoryTheory.DerivedCategory.IdealPower.HomologySystem.adicLimit_of_isPseudoCoherent
