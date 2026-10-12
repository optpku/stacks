/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Evaluation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (M : LeftDifferentialGradedModule A)
variable (N : CochainComplex (ModuleCat.{v} R) ℤ)

/- Remark 22.13.5 (0FQ7): ordinary evaluation transposes to the canonical left-DG-module
map from `M` into its double internal Hom. -/
@[stacks 0FQ7] #check
  (OfLeft.evaluation M N : M ⟶ OfRight.obj (OfLeft.obj M N) N)

#check @OfLeft.evaluationPairing
#check @OfLeft.evaluationPairing_tmul
#check @OfLeft.evaluation_transpose
#check @OfLeft.evaluation_apply

end DifferentialGradedModule.InternalHom
