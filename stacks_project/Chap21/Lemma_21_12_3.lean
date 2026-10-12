/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

/- Lemma 21.12.3 (03FC): the generic ringed-site Čech API owns the degree-zero evaluation
comparison and injective positive-degree vanishing.  This source-facing file intentionally keeps
only the tagged checks; no chapter-specific wrapper is needed. -/
@[stacks 03FC]
#check @SheafOfModules.RingedSite.Cech.zero_isomorphic_evaluation

@[stacks 03FC "positive successor degrees"]
#check @SheafOfModules.RingedSite.Cech.isZero_of_injective_succ

#check @SheafOfModules.RingedSite.Cech.isZero_of_injective_of_pos
