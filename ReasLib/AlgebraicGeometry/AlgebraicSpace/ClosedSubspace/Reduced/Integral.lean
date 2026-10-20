/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Space
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral

/-! # Integrality of reduced closed images

The reduced closed image on an irreducible closed subset of a decent algebraic
space is integral.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The reduced closed image on an irreducible closed subset of a decent algebraic
space is integral. -/
instance ReducedClosed.Space.instIsIntegral_irreducibleClosed {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ReducedClosed.Space.space X (Closeds.mk (T : Set (Points X)) T.isClosed)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
