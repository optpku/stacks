/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.ShortExact
import StacksCheckRecall

@[expose] public section

/- Lemma 13.16.5 is owned by the reusable short-exact-sequence API for
`Functor.RightAcyclic.Bounded`. Its generic epi-only conclusion is owned
one layer lower by `Functor.shortExact_of_preservesFiniteLimits`. -/
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.isClosedUnderExtensions
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.middle_of_shortExact
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.epi_map_g_of_ends
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.map_shortExact_of_ends
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.cokernel_of_shortExact
@[stacks 015D] #check @CategoryTheory.Functor.RightAcyclic.Bounded.map_shortExact_of_left_middle
@[stacks 015D] #check
  @CategoryTheory.Functor.RightAcyclic.Bounded.kernel_of_shortExact_of_epi_map_g
@[stacks 015D] #check @CategoryTheory.Functor.shortExact_of_preservesFiniteLimits

end
