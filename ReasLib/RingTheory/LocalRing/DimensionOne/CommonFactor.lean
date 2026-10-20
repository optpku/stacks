/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import ReasLib.Algebra.Module.IdealPower.Predicate

/-!
# Common factors in finite extensions of one-dimensional local rings
-/

@[expose] public section

universe u

namespace IsLocalRing.DimensionOne

/-- Two nonzerodivisors in a one-dimensional Noetherian local ring acquire a common
nonzerodivisor factor in a finite injective extension with power-torsion cokernel, and
the residual factors generate the unit ideal. -/
theorem exists_finiteExtension_commonFactor
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (a b : R)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S),
      Function.Injective (algebraMap R S) ∧
        Module.IsAnnihilatedByPower (IsLocalRing.maximalIdeal R)
          (S ⧸ (Algebra.linearMap R S).range) ∧
        ∃ t a' b' : S,
          t ∈ nonZeroDivisors S ∧ a' ∈ nonZeroDivisors S ∧ b' ∈ nonZeroDivisors S ∧
            algebraMap R S a = t * a' ∧ algebraMap R S b = t * b' ∧
              Ideal.span ({a', b'} : Set S) = ⊤ := sorry

end IsLocalRing.DimensionOne
