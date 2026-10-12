/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Transitivity
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.31.5 (0E1Y): a tower of sheaves of commutative rings has a canonical comparison
map and a map from the base-changed naive cotangent complex to its mapping cocone.  The latter is
an isomorphism on `H⁰` and an epimorphism on `H⁻¹`, producing the canonical six-term exact
sequence. -/
@[stacks 0E1Y]
#check @SheafOfModules.RingedSite.NaiveCotangent.transitivity

#check @SheafOfModules.RingedSite.NaiveCotangent.Transitivity

#check @SheafOfModules.RingedSite.NaiveCotangent.baseChange

#check @SheafOfModules.RingedSite.NaiveCotangent.Presentation.nullHomotopy

#check @SheafOfModules.RingedSite.NaiveCotangent.Presentation.toCocone

#check @SheafOfModules.RingedSite.NaiveCotangent.Transitivity.sixTerm

#check @SheafOfModules.RingedSite.NaiveCotangent.Transitivity.sixTerm_exact

#check @SheafOfModules.RingedSite.NaiveCotangent.Transitivity.comparison_zero_epi
