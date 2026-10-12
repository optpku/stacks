/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Colimit.Finiteness
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Exercise 111.2.9 (1): any module is the directed colimit of its finitely generated
submodules, via the inclusion system `Module.fgSystem` of `{N : Submodule R M // N.FG}`. -/
@[stacks 02CP]
#check @Module.fgSystem.equiv

/- Exercise 111.2.9 (2): any module is in some way a filtered colimit of finitely presented
modules, i.e. it lies in `(ModuleCat.isFinitePresentation R).ind`. -/
@[stacks 02CP]
#check @ModuleCat.isFinitePresentation_ind
