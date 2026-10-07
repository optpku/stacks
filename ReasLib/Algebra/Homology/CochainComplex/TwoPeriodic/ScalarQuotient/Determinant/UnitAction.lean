module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Determinant
import ReasLib.Algebra.Module.FiniteLength.Determinant.UnitAction

/-!
# Unit Actions on Scalar Quotient Determinants

This file computes scalar quotient determinants when the first scalar is a unit.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- For a unit `u` and a regular scalar `b` on a finite dimension-one module `M`, the
scalar quotient determinant is the residue of `u` raised to the length of `M ⧸ b • ⊤`. -/
theorem scalarQuotientDeterminant_unit_left
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (u : Aˣ) (b : A) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M (u : A) b (u.isSMulRegular M) hb hdim =
      Units.map (IsLocalRing.residue A).toMonoidHom u ^
        (Module.length A (QuotSMulTop b M)).toNat := sorry

/-- For a unit `u` and a nonzerodivisor `b` in a one-dimensional Noetherian local ring,
the scalar quotient determinant is the residue of `u` raised to the order of `b`. -/
theorem scalarQuotientSelfDeterminant_unit_left
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (u : Aˣ) (b : A) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1) :
    scalarQuotientSelfDeterminant (u : A) b u.isUnit.mem_nonZeroDivisors hb hdim =
      Units.map (IsLocalRing.residue A).toMonoidHom u ^ (Ring.ord A b).toNat := sorry

end CategoryTheory.TwoPeriodicEndomorphism
