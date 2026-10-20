module

public import ReasLib.FieldTheory.GeometricRegularity.Smooth
import StacksCheckRecall

/-!
# Lemma 10.166.4

@stack 07QF
-/

@[expose] public section

/- Lemma 10.166.4 [stacks 07QF]: canonical recall that smooth algebras preserve geometric
regularity over a field. -/
@[stacks 07QF]
#check @Algebra.IsGeometricallyRegular.of_smooth

/- The field-base specialization is available as the canonical typeclass instance from the same
shared leaf. -/
@[stacks 07QF]
#check @Algebra.Smooth.instIsGeometricallyRegular_of_field
