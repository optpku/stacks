module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal
import StacksCheckRecall

/-!
# Principal power torsion and two-term towers

The reusable owner is the endomorphism-power tower specialized to multiplication by `f` on the
regular module. This chapter file records the three source clauses without rebuilding singleton
Koszul cones or sequential pro-morphism representatives.

@stack 091X
-/

@[expose] public section

/- Lemma 15.94.1 (1): bounded `f`-power torsion supplies the reverse maps from shifted principal
quotients to the two-term complexes; the canonical forward maps are the augmentation system. -/
#check @CategoryTheory.End.Power.augmentationSystem
@[stacks 091X "(1) shifted inverse from bounded power torsion"]
#check @CategoryTheory.DerivedCategory.PrincipalPower.existsShiftInverse

/- Lemma 15.94.1 (2): these forward and shifted reverse maps identify the two sequential
pro-objects. -/
@[stacks 091X "(2) principal power pro-isomorphism"]
#check @CategoryTheory.DerivedCategory.PrincipalPower.augmentation_isIso

/- Lemma 15.94.1 (3): a Noetherian ring has a positive cutoff bounding principal power torsion. -/
@[stacks 091X "(3) Noetherian stable cutoff"]
#check @CategoryTheory.DerivedCategory.PrincipalPower.existsStableCutoff_of_isNoetherian

/- The categorical cokernel tower is the explicit tower of principal-power quotients. -/
#check @CategoryTheory.DerivedCategory.PrincipalPower.cokernelSystem_isIsomorphic
#check @Module.IsPowerTorsionStableAt
