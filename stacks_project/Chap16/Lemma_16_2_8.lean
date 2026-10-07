module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Factorization.SingularIdeal

@[expose] public section

/- Lemma 16.2.8: an algebra map whose image of the singular ideal is the unit
ideal factors through a smooth algebra. -/
@[stacks 07EU]
#check @AlgHom.Factorisation.Smooth.nonempty_of_map_singularIdeal_eq_top
