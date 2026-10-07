module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.16.3

The finite representable basis and its induced cohomology test set are reusable site APIs in
`GrothendieckTopology.Cohomology`; this chapter entry only recalls them.
-/

open CategoryTheory CategoryTheory.Limits

/- Remark 21.16.3 (0GN4): a finite cover-refinement basis with the additional equalizer-cover
condition yields a cohomology test set consisting of finite coproducts of sheafified representables.
-/
@[stacks 0GN4]
#check @CategoryTheory.GrothendieckTopology.Cohomology.Basis.toTestSet

#check @CategoryTheory.GrothendieckTopology.Cohomology.Basis
#check @CategoryTheory.GrothendieckTopology.Cohomology.basis_iff
#check @CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet.finiteRepresentableCoproducts

end
