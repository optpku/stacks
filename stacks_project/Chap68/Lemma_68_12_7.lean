/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Dimension along locally quasi-finite morphisms of algebraic spaces

A locally quasi-finite morphism of algebraic spaces cannot increase global
dimension, in the sense of `AlgebraicSpace.dimension`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a locally quasi-finite
morphism of algebraic spaces over `S`. Then `dimension X ≤ dimension Y`. -/
@[stacks 0ED0]
theorem dimension_le_of_locallyQuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyQuasiFinite f] :
    dimension X ≤ dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
