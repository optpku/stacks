module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.SubmoduleTower
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.119.4

The reusable owner is the determinant comparison for a finite-projective submodule tower in
`ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.SubmoduleTower`. Its quotient row is modeled
directly by the canonical maps `L / K → M / K → M / L`.

@stack 0FJD
-/

noncomputable section

open scoped Module.Determinant TensorProduct

/- Lemma 15.119.4: determinant comparisons are coherent along a submodule tower. -/
@[stacks 0FJD "Lemma 15.119.4: determinant comparison for a submodule tower"]
#check @Module.Determinant.SubmoduleTower.commutes

#check @Submodule.Tower.quotientInclusion
#check @Submodule.Tower.quotientProjection
#check @Submodule.Tower.exact_quotientInclusion_quotientProjection
#check @Module.Determinant.SubmoduleTower.leftIso
#check @Module.Determinant.SubmoduleTower.rightIso
#check @Module.Determinant.SubmoduleTower.totalIso
#check @Module.Determinant.SubmoduleTower.quotientIso
#check @Module.Determinant.SubmoduleTower.commutes_apply

end
