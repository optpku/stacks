/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Torsion
import StacksCheckRecall

@[expose] public section

/-!
# Injectivity Detected by a Finite Principal-Open Family

@stack 0565

The Cech-family map, its scalar-multiplication comparison, and the intervening torsion criterion
are all owned by ReasLib.  This chapter item is therefore a direct semantic recall.
-/

@[stacks 0565 "principal-open family-map zero criterion"]
#check @LocalizedModule.Away.Cech.familyMap_apply_eq_zero_iff_exists_pow_smul_eq_zero

@[stacks 0565 "principal-open family-map injectivity via torsion"]
#check @LocalizedModule.Away.Cech.familyMap_injective_iff_torsionBySet_eq_bot

/- Lemma 10.24.4 (0565): for a finite family, injectivity of the map to the family of away
localizations is equivalent to injectivity of coordinatewise multiplication by the denominators.
Finite products are the canonical Lean model of the source's finite direct sums. -/
@[stacks 0565 "localization and scalar-family injectivity comparison"]
#check @LocalizedModule.Away.Cech.familyMap_injective_iff_smulFamilyMap_injective

#check @LocalizedModule.Away.Cech.smulFamilyMap
#check @LocalizedModule.Away.Cech.ker_smulFamilyMap

end
