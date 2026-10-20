/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

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

/-- Pullback along a morphism of algebraic spaces flat at a point detects relative flatness
of a quasi-coherent module at the image point. -/
@[stacks 05VY]
theorem flatOverAt_iff_pullback_flatOverAt_of_flatAt (G : Y.Modules) [G.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (hf : FlatAt f x) :
    flatOverAt G g (Points.map f x) ↔
      flatOverAt ((pullback f).obj G) (f ≫ g) x :=
  sorry

/-- Pullback along a flat surjective morphism of algebraic spaces detects relative flatness
of a quasi-coherent module over the target. -/
@[stacks 05VY]
theorem flatOver_iff_pullback_flatOver_of_surjective_of_flat (G : Y.Modules)
    [G.IsQuasicoherent] (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Surjective f] :
    flatOver G g ↔ flatOver ((pullback f).obj G) (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
