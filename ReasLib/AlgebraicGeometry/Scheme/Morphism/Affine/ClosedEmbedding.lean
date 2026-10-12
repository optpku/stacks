/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affineness from a closed embedding of underlying spaces

A closed embedding of the underlying topological spaces forces a scheme morphism to be affine.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- If the underlying map of a scheme morphism is a closed embedding, then the morphism is
affine. -/
theorem isAffineHom_of_base_isClosedEmbedding
    (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding ⇑(ConcreteCategory.hom f.base)) :
    IsAffineHom f := by
  exact isAffineHom_of_isInducing f hf.isInducing hf.isClosed_range

end AlgebraicGeometry
