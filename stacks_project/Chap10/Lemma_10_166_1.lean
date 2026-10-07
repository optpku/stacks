module

public import ReasLib.FieldTheory.GeometricRegularity.EssFiniteType
import StacksCheckRecall

/-!
# Lemma 10.166.1

@stack 0381
-/

@[expose] public section

/- Lemma 10.166.1 [stacks 0381]: canonical recall of the owner-level criterion for geometric
regularity after essentially finite type field extensions. -/
@[stacks 0381]
#check @Algebra.IsGeometricallyRegular.iff_forall_essFiniteType_tensorProduct_isRegularRing

/- Lemma 10.166.1 [stacks 0381]: canonical recall of the equivalent finite purely inseparable
field-extension test. -/
@[stacks 0381]
#check @Algebra.IsGeometricallyRegular.forall_essFiniteType_tensorProduct_isRegularRing_iff_forall_finite_purelyInseparable
