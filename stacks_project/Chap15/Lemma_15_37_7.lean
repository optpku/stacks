module

public import ReasLib.RingTheory.Smooth.Topological
import StacksCheckRecall

/-!
# Lemma 15.37.7 (07EF)

@stack 07EF
-/

@[expose] public section

/- Lemma 15.37.7 (07EF): topological formal smoothness is stable under composition. -/
@[stacks 07EF "composition of topologically formally smooth maps"]
#check @RingHom.FormallySmoothTopologically.comp
