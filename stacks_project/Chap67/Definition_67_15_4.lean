module

public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/- Definition 67.15.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `F` be a finite type quasi-coherent `𝒪_X`-module. The scheme-theoretic support
of `F` is the closed subspace `Z ⊂ X` constructed in Lemma 67.15.3. -/
@[stacks 07U1] #check (schemeTheoreticSupport F : ClosedSubspace X)
