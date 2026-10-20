/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# Quasi-finite points in fibers of algebraic spaces

For a finite-type morphism of algebraic spaces, the points in a fixed fiber
at which the morphism is quasi-finite form a finite set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a finite-type morphism of algebraic spaces over a scheme, the points
lying over any fixed target point at which the morphism is quasi-finite form
a finite set. -/
@[stacks 0ABN]
theorem FiniteType.finiteQuasiFiniteAtPointsOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] (y : Points Y) :
    (setOf fun x : Points X ↦ Points.map f x = y ∧ QuasiFiniteAt f x).Finite := sorry

end AlgebraicGeometry.AlgebraicSpace
