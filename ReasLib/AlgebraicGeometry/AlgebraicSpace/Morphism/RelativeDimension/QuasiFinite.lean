/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Locally quasi-finite morphisms of algebraic spaces and relative dimension zero

A locally finite-type morphism of algebraic spaces is locally quasi-finite
exactly when it has relative dimension zero at every source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite-type morphism of algebraic spaces is locally quasi-finite
if and only if it has relative dimension zero at every source point. -/
@[stacks 04NV]
theorem locallyQuasiFinite_iff_relativeDimension_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ RelativeDimension f 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
