/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Basis
import StacksCheckRecall

@[expose] public section

/- Lemma 6.33.2: every gluing datum of sheaves of sets on an open cover is realized by a sheaf
on the ambient space. This is the `Type` specialization of the algebraic descent theorem, whose
explicit realization is `Gluing.basisSheafExtend`. -/
@[stacks 00AL]
recall TopCat.Sheaf.OpenCover.Gluing.existsRealizingSheaf
