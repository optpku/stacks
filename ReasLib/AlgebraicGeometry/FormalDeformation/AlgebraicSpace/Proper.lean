/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.DualNumber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-! # Finite-dimensional deformation spaces of proper algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))
variable [AlgebraicSpace.Proper (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X)]

/-- The infinitesimal automorphism space of a proper algebraic space over a field is
finite-dimensional over that field. -/
instance instFiniteDimensional_inf : FiniteDimensional k (inf Λ k X) := sorry

/-- The tangent space of the deformation category of a proper algebraic space over a field is
finite-dimensional over that field. -/
instance instFiniteDimensional_tangentSpace :
    FiniteDimensional k (tangentSpace Λ k X) := sorry

end FlatAlgebraicSpaceCat
