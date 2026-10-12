/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.54.1: if `X` is a ringed space, `I` is an injective `𝒪_X`-module, and `E` is a
finite locally free `𝒪_X`-module, then `E ⊗ I` is injective. -/
@[stacks 01E7]
#check @SheafOfModules.IsFiniteLocallyFree.tensor_injective
