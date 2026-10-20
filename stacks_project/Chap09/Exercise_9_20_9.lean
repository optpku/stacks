module

public import ReasLib.FieldTheory.Discriminant.Quadratic
import StacksCheckRecall

@[expose] public section

/- Domain-style sampling for Exercise 9.20.9:
- primary domain: quadratic field extensions, discriminant classes, and the separable / purely
  inseparable dichotomy;
- canonical owner: `FieldExtension.discriminant K L : SquareClassWithZero K` and the
  quadratic-extension
  normal-form API in `FieldTheory.Discriminant.Quadratic`;
- source-facing role: assemble the three explicit Stacks cases and prove that they are mutually
  exclusive. The calculations of trace normal forms, power-basis discriminants, and primitive
  generators belong to the shared owner.
-/

open scoped IntermediateField
open FieldExtension
open FieldExtension.QuadraticExtension

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

variable {K L}

section Quadratic

variable [Algebra.IsQuadraticExtension K L]

-- Local declaration justification (source-local notation): the three source cases repeatedly
-- display the same extension discriminant and remain local to this textbook exercise.
local notation "Δ" => FieldExtension.discriminant K L
-- Local declaration justification (source-local notation): this is the literal first case in the
-- source trichotomy and is used only to keep that statement readable.
local notation "purelyInseparableCase" =>
  Δ = SquareClassWithZero.mk K 0 ∧ ringChar K = 2 ∧ IsPurelyInseparable K L ∧
    ∃ x : L, x ^ 2 ∈ (⊥ : IntermediateField K L) ∧ K⟮x⟯ = ⊤
-- Local declaration justification (source-local notation): this is the literal second case in
-- the source trichotomy and is used only to keep that statement readable.
local notation "separableCase" =>
  Δ = SquareClassWithZero.mk K 1 ∧ ringChar K = 2 ∧ Algebra.IsSeparable K L
-- Local declaration justification (source-local notation): this is the literal third case in the
-- source trichotomy and is used only to keep that statement readable.
local notation "nonsquareCase" =>
  Δ ≠ SquareClassWithZero.mk K 1 ∧ ringChar K ≠ 2 ∧
    ∃ y : L, ∃ a : K, Δ = SquareClassWithZero.mk K a ∧
      y ^ 2 = algebraMap K L a ∧ K⟮y⟯ = ⊤

namespace QuadraticExtensionDiscriminant

/-- Exercise 9.20.9 (1): every quadratic extension lies in the purely inseparable,
characteristic-two separable, or nonsquare-discriminant case. -/
@[stacks 0BIN]
theorem exhaustive : purelyInseparableCase ∨ separableCase ∨ nonsquareCase := by
  by_cases hsep : Algebra.IsSeparable K L
  · by_cases hchar : ringChar K = 2
    · have hdisc : Δ = SquareClassWithZero.mk K 1 :=
        discriminantEqOneOfIsSeparableAndRingCharEqTwo
          (K := K) (L := L) hsep hchar
      exact Or.inr <| Or.inl ⟨hdisc, hchar, hsep⟩
    · have hdisc_ne : Δ ≠ SquareClassWithZero.mk K 1 :=
        discriminantNeOneOfRingCharNeTwo (K := K) (L := L) hchar
      obtain ⟨y, a, hdisc, hy, hy_top⟩ :=
        existsDiscriminantSquareRootGeneratorOfRingCharNeTwo (K := K) (L := L) hchar
      exact Or.inr <| Or.inr ⟨hdisc_ne, hchar, ⟨y, a, hdisc, hy, hy_top⟩⟩
  · obtain ⟨hpure, hchar⟩ :=
      isPurelyInseparableAndRingCharEqTwoOfNotSeparable
        (K := K) (L := L) hsep
    have hdisc : Δ = SquareClassWithZero.mk K 0 :=
      discriminantEqZeroOfNotSeparable (K := K) (L := L) hsep
    obtain ⟨x, hx_square, hx_top⟩ :=
      existsSquareGeneratorOfIsPurelyInseparable (K := K) (L := L) hpure
    exact Or.inl ⟨hdisc, hchar, hpure, ⟨x, hx_square, hx_top⟩⟩

/-- Exercise 9.20.9 (2): the purely inseparable and separable cases are incompatible. -/
theorem purelyInseparableCaseIncompatibleWithSeparableCase :
    ¬ (purelyInseparableCase ∧ separableCase) := by
  rintro ⟨hpure, hsep⟩
  exact (notSeparableOfIsPurelyInseparable
    (K := K) (L := L) hpure.2.2.1) hsep.2.2

/-- Exercise 9.20.9 (3): the purely inseparable and nonsquare cases are incompatible. -/
theorem purelyInseparableCaseIncompatibleWithNonsquareCase :
    ¬ (purelyInseparableCase ∧ nonsquareCase) := by
  rintro ⟨hpure, hnonsquare⟩
  exact hnonsquare.2.1 hpure.2.1

/-- Exercise 9.20.9 (4): the separable characteristic-two and nonsquare cases are incompatible. -/
theorem separableCaseIncompatibleWithNonsquareCase :
    ¬ (separableCase ∧ nonsquareCase) := by
  rintro ⟨hsep, hnonsquare⟩
  exact hnonsquare.2.1 hsep.2.1

end QuadraticExtensionDiscriminant

end Quadratic
