/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Descent
import StacksCheckRecall

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

/- Lemma 67.31.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `G` be a quasi-coherent sheaf on `Y`. Let `x ∈ |X|` with image
`y ∈ |Y|`. If `f` is flat at `x`, then `G` is flat over `Z` at `y` if and only if
`(pullback f).obj G` is flat over `Z` at `x`. -/
@[stacks 05VY]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff_pullback_flatOverAt_of_flatAt :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (G : Y.Modules) [G.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (hf : FlatAt f x),
    flatOverAt G g (Points.map f x) ↔
      flatOverAt ((pullback f).obj G) (f ≫ g) x)

/- Lemma 67.31.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `G` be a quasi-coherent sheaf on `Y`. If `f` is surjective and
flat, then `G` is flat over `Z` if and only if `(pullback f).obj G` is flat over `Z`. -/
@[stacks 05VY]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOver_iff_pullback_flatOver_of_surjective_of_flat :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (G : Y.Modules)
    [G.IsQuasicoherent] (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Surjective f],
    flatOver G g ↔ flatOver ((pullback f).obj G) (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace.Modules
