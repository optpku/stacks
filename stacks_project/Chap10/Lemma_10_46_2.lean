module

public import ReasLib.FieldTheory.PrimeField.PowerCriterion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.2

@stack 0BR7

The root-of-unity and finite-field calculations in the textbook proof are not chapter-level
mathematical objects.  The reusable statement is the field-extension criterion owned by
`FieldExtension.iff_forall_pow_mem_range`; the exceptional alternative is exposed through
`FieldExtension.IsPrimeAlgebraic`.
-/

/- Lemma 10.46.2 (Tag 0BR7): positive powers in the source image. -/
@[stacks 0BR7]
#check @FieldExtension.iff_forall_pow_mem_range

#check @FieldExtension.IsPrimeAlgebraic
#check @FieldExtension.isPrimeAlgebraic_of
#check @FieldExtension.iff_isPowerSurjective
#check @RingHom.IsPowerSurjective
#check @RingHom.isIntegral_of_isPowerSurjective
