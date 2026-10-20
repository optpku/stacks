/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

/-!
# Finite irreducible components of affine étale charts

An affine étale chart over a decent algebraic space with finitely many
irreducible components also has finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine scheme étale over a decent algebraic space with finitely many
irreducible components, viewed via `ofOver`, has finitely many irreducible
components. -/
theorem HasFiniteIrreducibleComponents.ofOver_etale {S : Scheme.{u}}
    {Y : AlgebraicSpace S} [IsDecent Y] [HasFiniteIrreducibleComponents Y]
    {V : Over S} [IsAffine V.left] (g : ofOver V ⟶ Y) [Etale g] :
    HasFiniteIrreducibleComponents (ofOver V) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
