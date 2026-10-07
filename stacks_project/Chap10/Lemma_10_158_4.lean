module

public import ReasLib.FieldTheory.Separable.Generated.Kaehler.CharP
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.4 [stacks 031X]: canonical recall of the characteristic-`p`
Kähler criterion for Stacks-separable field extensions.

@stack 031X
-/

@[stacks 031X]
#check @Algebra.IsSeparableOver.CharP.iff_mapBaseChange_injective
