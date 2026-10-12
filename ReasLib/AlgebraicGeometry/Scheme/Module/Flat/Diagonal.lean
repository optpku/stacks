/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import ReasLib.RingTheory.Etale.Weakly.Flat

/-!
# Flatness from a flat diagonal

A module sheaf that is flat relative to a scheme morphism is intrinsically flat when the
morphism's diagonal is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFlat

/-- If the diagonal of a scheme morphism is flat, then a module sheaf flat over its target is
intrinsically flat over its source. -/
theorem of_flatOver_of_flat_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℱ : X.Modules) [Flat (pullback.diagonal f)] (hℱ : flatOver ℱ f) : ℱ.IsFlat := sorry

end AlgebraicGeometry.Scheme.Modules.IsFlat
