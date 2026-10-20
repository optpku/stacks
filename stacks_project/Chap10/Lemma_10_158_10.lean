module

public import ReasLib.FieldTheory.Separable.Generated.SmoothSubalgebra
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.10 [stacks 037X]: canonical recall of the smooth
fraction-field model criterion for an essentially finite-type field extension.

@stack 037X
-/

@[stacks 037X]
#check @Algebra.IsSeparableOver.iff_exists_smooth_subalgebra_isFractionRing
