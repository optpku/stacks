/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.IsoClass
import StacksCheckRecall

/-!
# Principal homogeneous space of square-zero solutions

If a diagram 91.2.0.1 admits at least one solution, isomorphism classes of
solutions are principal homogeneous under Ext¹_B(NL_{B/A}, N).
-/

universe u

/-
Lemma 91.2.2 If there exists a solution to 91.2.0.1, then the set of
isomorphism classes of solutions is principal homogeneous under
Ext¹_B(NL_{B/A}, N), represented by the naive cotangent Ext¹ model.
-/
@[stacks 08S7] #check
  (RingHom.SquareZeroExtension.isoClassEquiv :
    ∀ {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B]
      [Algebra A B] [AddCommGroup N] [Module B N] [Module A N]
      [IsScalarTower A B N] {π : A' →+* A} [π.IsSquareZeroExtension]
      {c : RingHom.SquareZeroExtension.KernelModule π →ₗ[A] N},
      RingHom.SquareZeroExtension.Solution (B := B) (N := N) π c →
        RingHom.SquareZeroExtension.extOneNaiveCotangent A B N ≃
          RingHom.SquareZeroExtension.IsoClass π B c)
