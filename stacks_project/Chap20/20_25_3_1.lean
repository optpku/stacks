/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Differential
import StacksCheckRecall

@[expose] public section

/- 20.25.3.1 (Tag 07MA): the summandwise differential of a tensor product of cochain complexes is
the graded Leibniz differential.  The reusable owner lives with the tensor-complex API. -/
@[stacks 07MA "tensor-complex differential on a bidegree summand"]
#check @HomologicalComplex.ιTensorObj_d

#check @HomologicalComplex.ιTensorObj_d_assoc
#print axioms HomologicalComplex.ιTensorObj_d
