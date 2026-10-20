/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Length along a closed immersion of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A quasi-coherent module on the source of a closed immersion of algebraic spaces has
length `d` at a point if and only if its direct image has length `d` at the image point. -/
@[stacks 0EE3]
theorem hasLengthAt_pushforward_closedImmersion (i : Y ⟶ X) [IsClosedImmersion i]
    (G : Y.Modules) [G.IsQuasicoherent] (y : Points Y) (d : ℕ∞) :
    hasLengthAt G y d ↔ hasLengthAt ((pushforward i).obj G) (Points.map i y) d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
