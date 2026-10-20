module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Quasi-compactness under 2-isomorphisms

Quasi-compactness of morphisms of algebraic stacks is invariant under
invertible 2-cells.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Quasi-compactness of morphisms of algebraic stacks is invariant under
2-isomorphism. -/
theorem iso_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (α : f ≅ g) :
    QuasiCompact f ↔ QuasiCompact g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
