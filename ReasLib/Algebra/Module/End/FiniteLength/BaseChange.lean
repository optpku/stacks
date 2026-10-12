/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.End.FiniteLength
public import ReasLib.RingTheory.LocalRing.Length.Fiber
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat local base change for finite-length determinants

The determinant of a base-changed finite-length endomorphism is the image of the original
determinant raised to the length of the closed fiber.

@stack 0GT0
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Module.End

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')] [Module.Flat R R']
variable [AddCommGroup M] [Module R M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) R'

/-- Lemma 15.121.3 (0GT0): flat local base change raises the source determinant to the length of
the closed fiber. -/
@[stacks 0GT0 "Lemma 15.121.3: finite-length determinant under flat local base change"]
theorem finiteLengthDeterminant_baseChange_pow_closedFiberLength
    (φ : Module.End R M) (hM : IsFiniteLength R M)
    (hClosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    (ResidueField.map (algebraMap R R') (φ.finiteLengthDeterminant hM)) ^
        (Module.length ClosedFiber ClosedFiber).toNat =
      finiteLengthDeterminant ((TensorProduct.isBaseChange R M R').endHom φ)
        ((IsLocalRing.isFiniteLength_baseChange_iff hClosedFiber).1 hM) := sorry
-- Proof strategy: base-change a stable composition series for `φ`; each source residue-field
-- factor becomes a closed-fiber module of length `Module.length ClosedFiber ClosedFiber`, and the
-- determinant of its base-changed factor map is the residue image of the source determinant to
-- that power. Multiply the factor formulas and use `finiteLengthDeterminant_eq_det` on both sides.

end Module.End

end
