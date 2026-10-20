module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap89.«89_3_0_1»

/-!
# Equivalence of the excision functor at a finite family of closed points

Base change along a finite family of elementary étale neighbourhoods of
pairwise distinct closed points of a decent algebraic space is an
equivalence of iso-over-open slice categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.3.1: let `S` be a scheme and `X` a decent algebraic space over
`S`. Let `x : ι → Points X` be a finite family of pairwise distinct closed
points, and let `U i` be elementary étale neighbourhoods of `x i`, shrunk
so that no point of `U i` maps to `x j` for `j ≠ i`. If each `(U i).hom` is
separated, then the functor `excisionFamilyFunctor X x hx U` of 89.3.0.1
is an equivalence of categories. The case of a single point is
`IsoOverOpen.baseChange_isEquivalence` (Lemma 70.19.1). -/
@[stacks 0BHB]
theorem excisionFamilyFunctor_isEquivalence {ι : Type} [Finite ι]
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) (hx_inj : Function.Injective x)
    (U : ∀ i, EtaleNeighborhood X (x i)) [∀ i, Separated (U i).hom]
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    (excisionFamilyFunctor X x hx U).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
