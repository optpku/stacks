module

public import ReasLib.RingTheory.Algebra.TensorProduct.FiniteStage
import StacksCheckRecall

@[expose] public section

/-!
# Finite Tensor Stages

Lemma 10.43.4 is a canonical recall of the finite-stage tensor-product API.
The reusable owner is independent of the chapter: it first exposes the map
from a pair of finitely generated subalgebras, then records the three distinct
obstructions as separate consequences.

@stack 00I3
-/

/- Lemma 10.43.4 (1) (Tag 00I3): nonreducedness of `R ⊗[k] S` occurs at a tensor product of
finitely generated `k`-subalgebras. -/
@[stacks 00I3]
#check @Algebra.TensorProduct.FGSubalgebraPair.exists_not_isReduced

/- Lemma 10.43.4 (2) (Tag 00I3): a nonzero zero divisor of `R ⊗[k] S` occurs at a tensor product
of finitely generated `k`-subalgebras. -/
@[stacks 00I3]
#check @Algebra.TensorProduct.FGSubalgebraPair.exists_nonzero_mul_eq_zero

/- Lemma 10.43.4 (3) (Tag 00I3): a nontrivial idempotent of `R ⊗[k] S` occurs at a tensor product
of finitely generated `k`-subalgebras. -/
@[stacks 00I3]
#check @Algebra.TensorProduct.FGSubalgebraPair.exists_nontrivial_idempotent

#check @Algebra.TensorProduct.FGSubalgebraPair.map
#check @Algebra.TensorProduct.FGSubalgebraPair.exists_lift
#check @Algebra.TensorProduct.FGSubalgebraPair.exists_lift_pair
