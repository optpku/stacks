module

public import ReasLib.FieldTheory.GeometricRegularity.Directed
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.166.5

@stack 07QG
-/

/- Lemma 10.166.5 [stacks 07QG]: canonical recall of directed-subfield descent for
geometric regularity. -/
@[stacks 07QG]
#check @Algebra.IsGeometricallyRegular.of_directed_iSup_subfields
