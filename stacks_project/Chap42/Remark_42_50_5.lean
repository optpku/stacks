module

import StacksCheckRecall
import stacks_project.Chap42.Lemma_42_50_2_DefinedChern

/- Remark 42.50.5: A localized-Chern `Situation` implies
`ChernClass.Derived.IsDefined E`, the more natural proposed replacement for its
technical condition. The source postpones constructing localized classes under
this weaker hypothesis until they are needed. -/
@[stacks 0GUK] #check @AlgebraicGeometry.LocalizedChern.Situation.isDefined
