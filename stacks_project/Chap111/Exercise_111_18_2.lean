module

public import stacks_project.Chap111.Definition_111_18_1
import StacksCheckRecall

@[expose] public section

/- Exercise 111.18.2: for Noetherian rings, Algebra Definition 10.105.1 catenarity
(`IsCatenaryRing`) agrees with Definition 111.18.1 height additivity of nested primes. -/
@[stacks 0CT5]
#check @isCatenaryRing_iff_height_additive
