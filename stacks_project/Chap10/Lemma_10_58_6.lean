module

public import ReasLib.RingTheory.GradedAlgebra.FiniteType
import StacksCheckRecall

/-!
# Lemma 10.58.6
@stack 00K0
-/

@[expose] public section

/-!
# Lemma 10.58.6

Component finiteness is owned by the reusable graded-module API, so the chapter entry is a
canonical recall.
-/

/- API design: `GradedModule.finitePiece` uses `Submodule R M` pieces and the shared degree-zero
module instance.  No source alias or local restriction-of-scalars instance is introduced. -/

/- Lemma 10.58.6 (Tag 00K0): every homogeneous piece of a finite graded module is finite over the
degree-zero component when the graded algebra is finite type over that component. -/
@[stacks 00K0]
#check @GradedModule.finitePiece
