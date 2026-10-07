module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.47.8: on a category C, a Grothendieck topology J is finer or stronger than J'
if and only if J' ≤ J, equivalently every covering sieve of J' is a covering sieve of J,
i.e. ∀ U, J' U ⊆ J U. In this case J' is coarser or weaker than J. -/
@[stacks 00Z6] #check GrothendieckTopology.instLEGrothendieckTopology
@[stacks 00Z6] #check GrothendieckTopology.instPartialOrder
#check GrothendieckTopology.le_def
