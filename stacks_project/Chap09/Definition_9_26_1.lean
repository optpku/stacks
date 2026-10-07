module

public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
import StacksCheckRecall

@[expose] public section

/- Definition 9.26.1 (Tag 030E): a purely transcendental extension is a field extension
`K / k` which is `k`-isomorphic to a multivariable rational function field. The shared
`FieldExtension` owner also supplies its transcendence-basis and algebraically independent
generating-family characterizations. -/
@[stacks 030E]
#check FieldExtension.IsPurelyTranscendental
#check FieldExtension.isPurelyTranscendental_iff_exists_isTranscendenceBasis
#check FieldExtension.isPurelyTranscendental_iff_exists_algebraicIndependent
#check FieldExtension.isPurelyTranscendental_adjoin_simple_of_transcendental
