/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.HomotopyLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.92.14: derived completeness of derived limits

The reusable formulation separates closure of derived completeness under homotopy limits from
the power-annihilation criterion that supplies derived completeness at each stage.

@stack 091W
-/

/- Lemma 15.92.14 (091W): a homotopy limit of a power-torsion inverse system is derived
complete with respect to the ideal. -/
@[stacks 091W "derived completeness of a power-torsion homotopy limit"]
#check @CategoryTheory.HomotopyLimit.IsOf.isDerivedComplete_of_powerTorsion

/- The underlying closure theorem, with stagewise derived completeness stated directly. -/
#check @CategoryTheory.HomotopyLimit.IsOf.isDerivedComplete

/- The object-level owner for a nilpotent ideal action. -/
#check @Ideal.IsNilpotentOn.isDerivedComplete

/- The source-facing bridge from the elementwise power formula. -/
#check @CategoryTheory.DerivedCategory.isDerivedComplete_of_pow_smul_id_eq_zero
