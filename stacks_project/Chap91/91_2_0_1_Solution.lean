/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Solution

universe u

section

variable {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B]
variable [Algebra A B] [AddCommGroup N] [Module B N] [Module A N]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (c : RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N)
variable [IsScalarTower A B N]

#check (RingHom.SquareZeroExtension.KernelModule π : Type u)
#check (RingHom.SquareZeroExtension.Solution π c : Type (u + 1))
#check (RingHom.SquareZeroExtension.Solution.of π c :
  ∀ {Bprime : Type u} [CommRing Bprime]
    (fromA' : A' →+* Bprime) (toB : Bprime →+* B)
    [toB.IsSquareZeroExtension]
    (comm_right : toB.comp fromA' =
      (algebraMap A B).comp π)
    (kernelEquiv : RingHom.SquareZeroExtension.KernelModule toB ≃ₗ[B] N),
    (∀ x : RingHom.SquareZeroExtension.KernelModule π,
      kernelEquiv (RingHom.SquareZeroExtension.kerMapOf π fromA' toB comm_right x) = c x) →
    RingHom.SquareZeroExtension.Solution π c)
#check (RingHom.SquareZeroExtension.Solution.spec π c :
  ∀ solution : RingHom.SquareZeroExtension.Solution π c,
    solution.toB.comp solution.fromA' =
      (algebraMap A B).comp π)

end
