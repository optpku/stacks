module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Shift
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DifferentialGradedModule

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (P : DifferentialGradedModule B) (k : ℤ)

/- Remark 22.30.2 (0FQR): the sign-free comparison identifies the shift of fixed-source
internal Hom with internal Hom into `P[k]`. -/
@[stacks 0FQR] #check
  (DifferentialGradedBimodule.internalHomShiftIso N P k :
    (DifferentialGradedBimodule.internalHom N P)[k] ≅
      DifferentialGradedBimodule.internalHom N (P[k]))
