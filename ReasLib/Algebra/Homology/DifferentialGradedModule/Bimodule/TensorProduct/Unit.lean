module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Unit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Regular DG Module as a Unit for Bimodule Tensor Products

The relative tensor unit for a left DG module is compatible with the right action carried by a
DG bimodule. This leaf upgrades the underlying cochain-complex isomorphism to an isomorphism of
right DG modules.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Evaluation by the left `A`-action is a morphism of right DG `B`-modules. -/
@[stacks 09LL "evaluation map for the bimodule tensor unit"]
def regularEvaluation (N : DifferentialGradedBimodule.{u, w, w, x} A B) :
    obj A.regularModule N ⟶ N.toRightModule where
  hom n :=
    ((DifferentialGradedModule.TensorProduct.regularTensorIso N.toLeftModule).hom.f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- Inserting the unit of `A` is a morphism of right DG `B`-modules. -/
@[stacks 09LL "coevaluation map for the bimodule tensor unit"]
def regularCoevaluation (N : DifferentialGradedBimodule.{u, w, w, x} A B) :
    N.toRightModule ⟶ obj A.regularModule N where
  hom n :=
    ((DifferentialGradedModule.TensorProduct.regularTensorIso N.toLeftModule).inv.f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- The regular right DG `A`-module is the tensor unit for a differential graded
`(A, B)`-bimodule, as an isomorphism of right DG `B`-modules. -/
@[stacks 09LL "regular DG module is the bimodule tensor unit"]
def regularTensorIso (N : DifferentialGradedBimodule.{u, w, w, x} A B) :
    obj A.regularModule N ≅ N.toRightModule where
  hom := regularEvaluation N
  inv := regularCoevaluation N
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Regular evaluation sends a pure tensor to the left action of its factors. -/
@[stacks 09LL "evaluation of a pure tensor at the bimodule tensor unit"]
theorem regularEvaluation_tmul (N : DifferentialGradedBimodule.{u, w, w, x} A B)
    (p q : ℤ) (a : A.X p) (x : N.X q) :
    (regularEvaluation N).hom (p + q) (tmul A.regularModule N a x) =
      N.leftMul p q a x := sorry

/-- Regular coevaluation sends an element to the pure tensor with the unit of `A`. -/
@[stacks 09LL "coevaluation at the bimodule tensor unit"]
theorem regularCoevaluation_apply (N : DifferentialGradedBimodule.{u, w, w, x} A B)
    (n : ℤ) (x : N.X n) :
    (regularCoevaluation N).hom n x =
      DifferentialGradedModule.TensorProduct.regularCoevaluationValue
        N.toLeftModule n x := sorry

end DifferentialGradedBimodule.Tensor
