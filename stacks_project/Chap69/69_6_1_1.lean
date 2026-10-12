/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.«69_6_1_1_Koszul»
import StacksCheckRecall

/- 69.6.1.1: if `f : U ⟶ X` is a surjective étale morphism of algebraic spaces, the
truncated Koszul complex `K^•(f)` of the trace `Tr_f : f_! ℤ̲ ⟶ ℤ̲`
has terms `K^i(f) = ⋀^{i+1}(f_! ℤ̲)`, and the displayed arrow is the
quasi-isomorphism `traceKoszulToConstant f : koszulComplex f ⟶ ℤ̲[0]` in
`Ab(X_étale)`. -/
@[stacks 0723] #check AlgebraicGeometry.AlgebraicSpace.traceKoszulToConstant
@[stacks 0723] #check AlgebraicGeometry.AlgebraicSpace.instQuasiIsoTraceKoszulToConstant
