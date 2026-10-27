/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite-dimensional deformation spaces of proper schemes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

/-- The infinitesimal automorphism space of a proper scheme over a field is
finite-dimensional over that field. -/
instance instFiniteDimensional_inf [AlgebraicGeometry.Flat hX] [IsProper hX] :
    FiniteDimensional k (inf Λ k X hX) := sorry

/-- The tangent space of the deformation category of a proper scheme over a field is
finite-dimensional over that field. -/
instance instFiniteDimensional_tangentSpace [AlgebraicGeometry.Flat hX] [IsProper hX] :
    FiniteDimensional k (tangentSpace Λ k X hX) := sorry

end FlatSchemeCat
