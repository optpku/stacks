module

public import stacks_project.Chap92.«92_27_0_1_Object»
import StacksCheckRecall

@[expose] public section

universe u

/- 92.27.0.1: objects of C_{X/Λ} are commutative diagrams X ← U over Spec(Λ) ← A,
where X is an algebraic space over Λ, U is a scheme, U ⟶ X is étale, and A is an
affine space 𝔸(ι; Spec(Λ)). -/
@[stacks 08VI]
#check (AlgebraicGeometry.AlgebraicSpace.Polynomial.Object :
  (R : CommRingCat.{u}) →
    AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec R) → Type (u + 1))
