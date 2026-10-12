/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.BasicOpen
import StacksCheckRecall

@[expose] public section

open PrimeSpectrum

/- Lemma 26.5.1 (1): inclusion of principal opens makes the larger generator invertible after
localization. -/
@[stacks 01HS] #check algebraMap_isUnit_of_basicOpen_le

/- Lemma 26.5.1 (2): inclusion of principal opens is detected by a positive-power divisibility
relation. -/
@[stacks 01HS] #check exists_pow_eq_mul_of_basicOpen_le

/- Lemma 26.5.1 (3): restriction between principal opens induces the canonical localization
homomorphism. -/
@[stacks 01HS] #check awayToAwayRingHom
#check awayToAwayAlgHom
#check awayToAwayAlgHom_self
#check awayToAwayAlgHom_comp
#check awayToAwayAlgHom_unique

/- Lemma 26.5.1 (4): localized modules restrict semilinearly over the localization
homomorphism. -/
@[stacks 01HS] #check awayToAwayModuleMap
#check awayToAwayModuleLinearMap
#check awayToAwayModuleLinearMap_self
#check awayToAwayModuleLinearMap_comp
#check awayToAwayModuleMap_mkLinearMap
#check awayToAwayModuleMap_unique

#check awayToAwayModuleMap_self_apply
#check awayToAwayModuleMap_comp_apply

/- Lemma 26.5.1 (5): an open cover of a principal open admits a finite principal-open
refinement. -/
@[stacks 01HS] #check basicOpen_has_finset_refinement_of_open_cover
#check basicOpen_has_finite_refinement_of_open_cover

/- Lemma 26.5.1 (6): a family of principal opens covers `D(f)` exactly when its images in `R_f`
span the unit ideal. -/
@[stacks 01HS] #check basicOpen_le_iSup_basicOpen_iff_span_eq_top
