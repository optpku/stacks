module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.ShortExact
import StacksCheckRecall

@[expose] public section

/- Lemma 13.16.5 is owned by the reusable short-exact-sequence API for
`Functor.RightAcyclic.Bounded`. Its generic epi-only conclusion is owned
one layer lower by `Functor.map_shortExact_of_epi_map_g`. -/
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.isClosedUnderExtensions
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.middle_of_shortExact
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.epi_map_g_of_ends
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.map_shortExact_of_ends
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.cokernel_of_shortExact
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.map_shortExact_of_left_middle
@[stacks 015D] #check
  @CategoryTheory.Functor.RightAcyclic.Bounded.kernel_of_shortExact_of_epi_map_g
@[stacks 015D] #check @CategoryTheory.Functor.map_shortExact_of_epi_map_g

end
