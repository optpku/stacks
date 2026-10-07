module

public import Mathlib.CategoryTheory.Filtered.Basic
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_12_8_Decent

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary

/-- The category of elementary étale neighbourhoods of a point of a decent algebraic space is
cofiltered. -/
instance instIsCofiltered {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    IsCofiltered (Elementary X x) := sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary
