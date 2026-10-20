module

public import ReasLib.FieldTheory.Normal.Finite
import StacksCheckRecall

@[expose] public section

/- Lemma 9.16.5 (Tag 0BMG): if `M/K` is normal and `M'/M` is finite inside a normal extension
`L/K`, then `M'` is contained in an intermediate field finite over `M` and normal over `K`. -/
@[stacks 0BMG]
#check FieldExtension.existsFiniteNormalIntermediateField
#check FieldExtension.existsFiniteNormalIntermediateFieldOfFiniteSet
#check FieldExtension.existsFiniteIntermediateFieldNormalOverBase
