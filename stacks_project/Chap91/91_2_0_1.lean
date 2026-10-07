module

public import ReasLib.RingTheory.RingHom.SquareZero.Solution
import StacksCheckRecall

universe u

/- 91.2.0.1: given a square-zero surjection π : A' →+* A with kernel I, an A-algebra B,
a B-module N whose A-action is restriction along A →+* B, and an A-linear map
c : I → N, a solution of the diagram
0 ⟶ N ⟶ ? ⟶ B ⟶ 0 over 0 ⟶ I ⟶ A' ⟶ A ⟶ 0 is a square-zero A'-algebra
surjection B' →+* B whose kernel is identified with N and which induces c. -/
@[stacks 08S4] #check (RingHom.SquareZeroExtension.Solution :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    {B : Type u} [CommRing B] [Algebra A B]
    (π : A' →+* A) [π.IsSquareZeroExtension]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N],
    (RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N) →
    ∀ [IsScalarTower A B N], Type (u + 1))
#check RingHom.SquareZeroExtension.Solution.of
#check RingHom.SquareZeroExtension.Solution.spec
