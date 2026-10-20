/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finiteness of proper relative de Rham cohomology

This module records the finite-module property of relative de Rham cohomology over a Noetherian
affine base for proper scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- For a proper morphism to the spectrum of a Noetherian ring, every integer-degree relative de
Rham cohomology module is finite over the base ring. -/
@[instance]
theorem cohomologyFinite {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec A) [IsProper p] (i : ℤ) :
    Module.Finite A (cohomologyOverAffineBase p i) := sorry

end AlgebraicGeometry.Scheme.DeRham
