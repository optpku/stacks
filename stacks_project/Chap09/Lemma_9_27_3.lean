module

public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCheckRecall

@[expose] public section

/- Lemma 9.27.3 (Tag 030M): for a normal algebraic extension, the relative separable and purely
inseparable parts are linearly disjoint and generate the whole extension.

The standard facts are `separableClosure.isPurelyInseparable`,
`perfectClosure.isPurelyInseparable`, and `separableClosure.isGalois`. The normal-case project
API is owned by `FieldExtension.PerfectClosure`. -/
#check separableClosure.isPurelyInseparable
#check perfectClosure.isPurelyInseparable
#check separableClosure.isGalois
#check FieldExtension.PerfectClosure.mem_iff_fixedByAllAut
#check FieldExtension.PerfectClosure.eq_fixedField_top_of_normal
#check FieldExtension.PerfectClosure.eq_bot_over
#check FieldExtension.PerfectClosure.isGalois_over
@[stacks 030M]
#check FieldExtension.PerfectClosure.separableInseparable_decomposition
