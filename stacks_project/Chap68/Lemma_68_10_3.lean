module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.FiniteLocallyFree
import StacksCheckRecall

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

/- Lemma 68.10.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a surjective finite
locally free morphism of algebraic spaces over `S`. For `y ∈ |Y|` the following
are equivalent: `y` is in the schematic locus of `Y`, and there exists an affine
open `U ⊂ X` containing the preimage of `y`. -/
@[stacks 0BA1] #check
  (AlgebraicGeometry.AlgebraicSpace.mem_schematicLocus_iff_exists_affineOpen :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [FiniteLocallyFree f]
    (y : Points Y),
    y ∈ (schematicLocus Y).pointsSet ↔
      ∃ U : OpenSubspace X, IsAffine U.X ∧ Points.map f ⁻¹' {y} ⊆ U.pointsSet)

end AlgebraicGeometry.AlgebraicSpace
