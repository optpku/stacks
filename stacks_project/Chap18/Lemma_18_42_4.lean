/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Completion
import StacksCheckRecall

/-!
# Adic completion of a constant sheaf

ReasLib owns the quotient towers, their module and commutative-ring limits,
the canonical completion map, sectionwise flatness, and reduction modulo the
defining ideal.
-/

@[expose] public section

/- Lemma 18.42.4 (093M) (1), flat-algebra clause: the completed commutative ring
sheaf is flat over the constant ring sheaf. -/
@[stacks 093M "(1)"]
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Ring.isFlat)

/- Lemma 18.42.4 (093M), canonical-identification clause: reduction of
completed sections modulo `I` is the constant `R / I` section module.  This
single canonical isomorphism represents the source's chain of quotient
presentations. -/
@[stacks 093M "(2)"]
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Module.reductionSheafIso)

/- The explicit inverse-limit and comparison data. -/
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Ring.map)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Module.sectionwiseFlat)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Module.sectionsIsoLimit)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Module.reductionComparison)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Module.reductionIso)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Ideal.sheaf)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Ideal.toCompletion)
#check (@CategoryTheory.ConstantSheaf.AdicCompletion.Ideal.range_app_eq_smulTop)
