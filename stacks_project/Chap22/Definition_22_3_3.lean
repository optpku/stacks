/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : ChainDGAlgebra.{u, v} R)

/- Definition 22.3.3 (061W): graded commutativity and strict commutativity use the same
Koszul-sign API for the chain and cochain models of a differential graded algebra. -/
@[stacks 061W]
#check (ChainDGAlgebra.IsCommutative A : Prop)
#check @ChainDGAlgebra.IsStrictlyCommutative
#check @CochainDGAlgebra.IsCommutative
#check @CochainDGAlgebra.IsStrictlyCommutative

/- Both models expose homogeneous computation lemmas for the Koszul sign and odd squares. -/
#check @ChainDGAlgebra.mul_comm_apply
#check @ChainDGAlgebra.mul_self_eq_zero_of_odd
#check @CochainDGAlgebra.mul_comm_apply
#check @CochainDGAlgebra.mul_self_eq_zero_of_odd
