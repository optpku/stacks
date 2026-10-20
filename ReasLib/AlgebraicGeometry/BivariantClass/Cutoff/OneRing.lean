module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.SumProduct
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# The separate cutoff-one convolution ring

Only cutoff one has the ambient degree-zero coefficient and entirely relative
positive coefficients. Its product is the already specified fixed-cutoff
convolution, rather than the product with addition of cutoff parameters.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cutoff

variable {S : Scheme.{u}} [UniversallyCatenary S]
  (δ : S → ℤ) [IsDimensionFunction δ]
  {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
  (f : Z ⟶ X) [IsClosedImmersion f.left]

/-- The specified cutoff-one convolution distributes over addition on the right. -/
theorem Family.oneMul_add (a b c : Family δ f 1) : a * (b + c) = a * b + a * c := sorry

/-- The specified cutoff-one convolution distributes over addition on the left. -/
theorem Family.add_oneMul (a b c : Family δ f 1) : (a + b) * c = a * c + b * c := sorry

/-- The specified cutoff-one convolution kills a zero left input. -/
theorem Family.zero_oneMul (a : Family δ f 1) : 0 * a = 0 := sorry

/-- The specified cutoff-one convolution kills a zero right input. -/
theorem Family.oneMul_zero (a : Family δ f 1) : a * 0 = 0 := sorry

/-- The cutoff-one ring, with pointwise addition and the existing concrete finite
convolution. Integer constants are integer multiples of its specified unit. -/
@[reducible] def Family.ringOne : Ring (Family δ f 1) where
  __ := (inferInstance : AddCommGroup (Family δ f 1))
  __ := Family.instMonoid δ f
  zero_mul := Family.zero_oneMul δ f
  mul_zero := Family.oneMul_zero δ f
  left_distrib := Family.oneMul_add δ f
  right_distrib := Family.add_oneMul δ f
  natCast n := n • Family.one δ f
  natCast_zero := by simp
  natCast_succ n := by
    change (n + 1) • Family.one δ f = n • Family.one δ f + Family.one δ f
    exact succ_nsmul (Family.one δ f) n
  intCast z := z • Family.one δ f
  intCast_ofNat n := by
    change (n : ℤ) • Family.one δ f = n • Family.one δ f
    exact natCast_zsmul (Family.one δ f) n
  intCast_negSucc n := by
    change (Int.negSucc n) • Family.one δ f = -((n + 1) • Family.one δ f)
    simp

/-- The full integer-degree cutoff-one ring is transferred along the explicitly
constructed restriction/zero-extension equivalence. No inverse is chosen. -/
@[reducible] def completedRingOne : Ring (Completed δ f 1) :=
  -- Local instance justification (defeq pin): Equiv.ring must transfer the named Family.ringOne convolution, so pin that structure only during this explicit transfer.
  letI := Family.ringOne δ f
  (completedEquivFamily δ f 1).toEquiv.ring

/-- The multiplication data of the full cutoff-one ring is the explicit old
convolution of nonnegative restrictions, followed by zero extension. -/
theorem completedRingOne_mul (a b : Completed δ f 1) :
    (completedRingOne δ f).mul a b =
      ofNonnegative δ f 1
        (Family.mul δ f (toNonnegative δ f 1 a) (toNonnegative δ f 1 b)) := rfl

/-- The unit data of the full cutoff-one ring is the old concrete unit series. -/
theorem completedRingOne_one :
    (completedRingOne δ f).one = ofNonnegative δ f 1 (Family.one δ f) := rfl

end AlgebraicGeometry.BivariantClass.Cutoff
