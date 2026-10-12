/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Descent of relative flatness of quasi-coherent modules on algebraic spaces

Pointwise relative flatness of a quasi-coherent module over a morphism of algebraic spaces is
detected by pullback along a morphism that is flat at the given point. Globally, pullback along
a surjective flat morphism detects relative flatness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- Lemma 67.31.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `G` be a quasi-coherent sheaf on `Y`. Let `x ∈ |X|` with image
`y ∈ |Y|`. If `f` is flat at `x`, then `G` is flat over `Z` at `y` if and only if
`(pullback f).obj G` is flat over `Z` at `x`. -/
@[stacks 05VY]
theorem flatOverAt_iff_pullback_flatOverAt_of_flatAt (G : Y.Modules) [G.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (hf : FlatAt f x) :
    flatOverAt G g (Points.map f x) ↔
      flatOverAt ((pullback f).obj G) (f ≫ g) x :=
  sorry

/-- Lemma 67.31.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `G` be a quasi-coherent sheaf on `Y`. If `f` is surjective and
flat, then `G` is flat over `Z` if and only if `(pullback f).obj G` is flat over `Z`. -/
@[stacks 05VY]
theorem flatOver_iff_pullback_flatOver_of_surjective_of_flat (G : Y.Modules)
    [G.IsQuasicoherent] (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Surjective f] :
    flatOver G g ↔ flatOver ((pullback f).obj G) (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
