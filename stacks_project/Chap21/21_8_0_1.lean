module

public import ReasLib.CategoryTheory.Sites.Cech.Computations
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicTopology

/- 21.8.0.1 (Tag 03AL): the differential of `cechComplex V family F` is the signed sum of
the coface maps encoded by `AlternatingCofaceMapComplex.objD`. -/
@[stacks 03AL "Cech differential as the alternating coface operator"]
#check @CategoryTheory.cechComplex_d_eq_objD

/- The reusable operator is definitionally the explicit sum
`∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i`. -/
#check @AlgebraicTopology.AlternatingCofaceMapComplex.objD

end
