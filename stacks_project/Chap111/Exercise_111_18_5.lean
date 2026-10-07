module

public import stacks_project.Chap111.Exercise_111_18_5_TwistedFlags
import StacksCheckRecall

/-!
# Exercise 111.18.5

A finite sober catenary space with no integer dimension function, realized by
the twisted two-flag Alexandrov space `TwistedFlags.Point`.
-/

@[expose] public section

open TopologicalSpace TwistedFlags

/- Exercise 111.18.5 (1): the constructed space is finite. -/
@[stacks 0CT6] #check (inferInstance : Finite Point)

/- Exercise 111.18.5 (2): the constructed space is sober. -/
@[stacks 0CT6] #check TwistedFlags.sober

/- Exercise 111.18.5 (3): the constructed space is catenary. -/
@[stacks 0CT6] #check (inferInstance : CatenarySpace Point)

/- Exercise 111.18.5 (4): the constructed space has no integer dimension function. -/
@[stacks 0CT6] #check TwistedFlags.not_exists_isDimensionFunction
