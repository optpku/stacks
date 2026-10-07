module

public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Point-fibre cardinality of universally bounded morphisms

A uniform bound on field-valued fibre degrees of a morphism from a scheme to an
algebraic space bounds the number of points in each fibre of `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.3.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`, and let
`U` be a scheme over `S`. Let `φ : U ⟶ X` be a morphism over `S`. If the fibres of
`φ` are universally bounded, then there exists an integer `n` such that each fibre of
`|U| → |X|` has at most `n` elements. -/
@[stacks 03JQ]
theorem exists_mapOfOver_fibre_encard_le_of_universallyBoundedFibres
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    (hφ : universallyBoundedFibres φ) :
    ∃ n : ℕ, ∀ x : Points X, (Points.mapOfOver φ ⁻¹' {x}).encard ≤ n :=
  sorry

/-- The integer bounding field-valued fibre degrees also bounds the number of points in
each fibre of the induced map `|U| → |X|`. -/
theorem degreesOfFibresBoundedBy.mapOfOver_fibre_encard_le
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
    {n : ℕ} (hf : degreesOfFibresBoundedBy f n) (x : Points X) :
    (Points.mapOfOver f ⁻¹' {x}).encard ≤ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
