/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

/- Definition 6.15.1: once the category `C` and the functor `F : C ⥤ Type w` are fixed, the
remaining axioms for a type of algebraic structure form the canonical property
`IsAlgebraicStructure C F`. The neutral support owner also exposes `isAlgebraicStructure_iff` and
the explicit constructor `isAlgebraicStructureOfProperties`; keeping those with the owner avoids
making later consumers depend on this numbered recall file. -/
@[stacks 007M]
recall IsAlgebraicStructure
