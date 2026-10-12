/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive.Normal
import StacksCheckRecall

/-!
# Lemma 15.23.19

@stack 0AVC

The reflexive hull is compared with the height-one localization intersection through the
canonical generic-fiber map owned by ReasLib.
-/

@[expose] public section

/- Canonical proofs supplying the two explicit bijectivity inputs of the data constructor. -/
#check @Module.Dual.genericLocalization_map_eval_bijective
#check @Module.genericLocalization_map_torsionQuotient_bijective

/- The proof-parametric map from the double dual into the generic localization of the torsion-free
quotient.  Its independence theorem makes the resulting comparison canonical. -/
#check @Module.Dual.toTorsionQuotientGenericLocalizationOf

/- Its defining compatibility with double-dual evaluation and the torsion-quotient map. -/
#check @Module.Dual.toTorsionQuotientGenericLocalizationOf_comp_eval

/- The compatibility condition uniquely characterizes the canonical comparison map. -/
#check @Module.Dual.toTorsionQuotientGenericLocalizationOf_unique

/- The comparison does not depend on the proofs used to package the two localized bijections. -/
#check @Module.Dual.toTorsionQuotientGenericLocalizationOf_congr

/- Lemma 15.23.19: the image of the double dual in the generic localization of the torsion-free
quotient is the intersection of its height-one localizations. -/
@[stacks 0AVC "Lemma 15.23.19"]
#check @Module.Dual.range_toTorsionQuotientGenericLocalization_eq_heightOneLocalizationIntersection
