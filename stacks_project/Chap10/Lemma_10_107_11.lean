module

public import ReasLib.RingTheory.Algebra.Epicenter.Matrix
import StacksCheckRecall

@[expose] public section

/-!
# Finite matrix criterion for the tensor-square equalizer

@stack 04VY

The reusable bundled witness and its proposition-valued existence wrapper are
owned by `Algebra.Epicenter`.
-/

@[stacks 04VY "finite matrix expression"]
#check @Algebra.Epicenter.MatrixExpr

@[stacks 04VY "existence of a finite matrix expression"]
#check @Algebra.Epicenter.HasMatrixExpr

@[stacks 04VY "finite matrix criterion"]
#check @Algebra.Epicenter.hasMatrixExpr_iff_tmul

@[stacks 04VY "epicenter membership criterion"]
#check @Algebra.Epicenter.mem_iff_hasMatrixExpr
