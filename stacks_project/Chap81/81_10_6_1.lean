module

public import stacks_project.Chap81.«81_10_6_1_Glueing»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.QCoh
open AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/- 81.10.6.1: the canonical functor QCoh(𝒪_X) ⟶ QCoh(Y → X, Z) sending F to
(F|_U, f^* F, can), where QCoh(Y → X, Z) is the category of triples (H, G, φ)
with H quasi-coherent on U = X \ Z, G quasi-coherent on Y, and
φ : (f|_V)^* H ≅ G|_V on V = Y \ f⁻¹Z. -/
@[stacks 0AEW] #check AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor
