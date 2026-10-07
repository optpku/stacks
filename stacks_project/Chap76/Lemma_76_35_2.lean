module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

/-!
# Finite neighbourhoods of quasi-finite fibres of proper morphisms

A proper morphism of algebraic spaces that is quasi-finite at every point
over a given point of the target is finite over some open neighbourhood of
that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.35.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `y : Points Y`. Assume `f` is proper, and `f`
is quasi-finite at all `x : Points X` lying over `y`. Then there exists an
open neighbourhood `V ⊂ Y` of `y` such that
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is finite.

The open neighbourhood is an open immersion `ι : V ⟶ Y` with
`y ∈ Set.range (Points.map ι)`, and the restricted morphism is
`openInverseImageTo f ι`. Quasi-finiteness at points of `X` is
`QuasiFiniteAt` in the sense of Stacks 67.27.1 (2). -/
@[stacks 0A4Y]
theorem exists_isFinite_openInverseImageTo_of_quasiFiniteAt_fiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (y : Points Y)
    (h : ∀ x : Points X, Points.map f x = y → QuasiFiniteAt f x) :
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
