module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree

/-!
# Schematic locus along a surjective finite locally free morphism

A point of the target of a surjective finite locally free morphism of algebraic
spaces lies in the schematic locus if and only if some affine open of the source
contains the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.10.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a surjective finite
locally free morphism of algebraic spaces over `S`. For `y ∈ |Y|` the following
are equivalent: `y` is in the schematic locus of `Y`, and there exists an affine
open `U ⊂ X` containing the preimage of `y`. -/
@[stacks 0BA1]
theorem mem_schematicLocus_iff_exists_affineOpen {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [FiniteLocallyFree f]
    (y : Points Y) :
    y ∈ (schematicLocus Y).pointsSet ↔
      ∃ U : OpenSubspace X, IsAffine U.X ∧ Points.map f ⁻¹' {y} ⊆ U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
