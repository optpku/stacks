/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Cofinite.GenericStalk
import StacksCheckRecall

@[expose] public section

/- Exercise 111.32.11 (1): the generic stalk functor on the infinite cofinite space
preserves finite products, equalizers, finite coproducts, and coequalizers. -/
@[stacks 0E9H] #check (CofiniteTopology.GenericStalk.exact :
  CategoryTheory.exactFunctor (CofiniteTopology.GenericStalk.space.Sheaf Type) Type
    CofiniteTopology.GenericStalk.stalkFunctor)

/- Exercise 111.32.11 (2): the generic stalk functor is not naturally isomorphic
to the spatial stalk functor at any point of the infinite cofinite space. -/
@[stacks 0E9H] #check (CofiniteTopology.GenericStalk.not_isIsomorphic_spatialStalk :
  ∀ x : CofiniteTopology.GenericStalk.space,
    ¬ CategoryTheory.IsIsomorphic CofiniteTopology.GenericStalk.stalkFunctor
      (CofiniteTopology.GenericStalk.spatialStalkFunctor x))

end
