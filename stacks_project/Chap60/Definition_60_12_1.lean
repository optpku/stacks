/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_12_1_Derivation
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/- Definition 60.12.1: in Situation 60.7.5, an `S`-derivation of the crystalline
structure sheaf into a crystalline module sheaf is the canonical
`CrystallineModuleSheaf.SDerivation` notion. -/
@[stacks 07IX] #check CrystallineModuleSheaf.SDerivation
