/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Fiber
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 91.2.7
For a square-zero surjection π : A' →+* A, an A-algebra B, a B-module N
with compatible A-action, and c : KernelModule π →ₗ[A] N, solution classes
are canonically bijective to the fibre of restriction on naive cotangent Ext¹
over the coefficient image of the tautological extension class.
-/
@[stacks 0GPX] #check (RingHom.SquareZeroExtension.isoClassFiberEquiv :
  ∀ {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A) [π.IsSquareZeroExtension]
    (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (c : RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N),
    RingHom.SquareZeroExtension.IsoClass π B c ≃
      RingHom.SquareZeroExtension.solutionExtFiber π B c)
