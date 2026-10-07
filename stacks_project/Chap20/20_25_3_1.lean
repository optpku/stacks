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
