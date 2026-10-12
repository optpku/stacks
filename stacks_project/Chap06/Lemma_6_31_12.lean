/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubsetExtensionByInitial
import StacksCheckRecall

@[expose] public section

/- Lemma 6.31.12 (1): extension by zero from an open subspace is fully faithful on sheaves of
modules. -/
@[stacks 00AB "module extension by zero is fully faithful"]
recall SheafOfModules.OpenSubset.ExtensionByZero.fullyFaithful

/- Lemma 6.31.12 (2): a sheaf of modules lies in the essential image of extension by zero from
an open subset exactly when all stalk modules away from it vanish. -/
@[stacks 00AB "essential image characterized by zero module stalks outside the open subset"]
recall SheafOfModules.OpenSubset.ExtensionByZero.essImage_iff
