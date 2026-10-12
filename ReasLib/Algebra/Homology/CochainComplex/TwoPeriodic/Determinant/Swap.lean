/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Swap

/-!
# Determinant Reciprocity under Swapping Differentials

This file records the reciprocity relation between the determinants of an exact finite-length
two-periodic endomorphism complex and the complex obtained by exchanging its differentials.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The determinants of an acyclic finite-length two-periodic endomorphism complex and of the
complex obtained by exchanging its differentials multiply to one. -/
@[stacks 02PL "determinant reciprocity under swapping differentials"]
theorem determinant_mul_swap
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic) :
    determinant K hM hK *
      determinant (swap K) hM ((swap_acyclic_iff K).2 hK) = 1 := sorry

end CategoryTheory.TwoPeriodicEndomorphism
