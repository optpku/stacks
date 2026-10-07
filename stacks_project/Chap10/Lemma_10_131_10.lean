module

public import ReasLib.RingTheory.Kaehler.Conormal
import StacksCheckRecall

/-!
# Lemma 10.131.10

@stack 02HP
-/

@[expose] public section

/- Lemma 10.131.10 [stacks 02HP]: canonical recall of the retraction of the conormal map
induced by an algebra section.  The exactness and right-surjectivity components are Mathlib's
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`KaehlerDifferential.mapBaseChange_surjective`. -/
@[stacks 02HP]
#check @KaehlerDifferential.Conormal.has_retraction_of_section

@[stacks 02HP]
#check @KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange

@[stacks 02HP]
#check @KaehlerDifferential.mapBaseChange_surjective
