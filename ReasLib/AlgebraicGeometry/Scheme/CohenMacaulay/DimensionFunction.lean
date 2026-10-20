/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Catenary
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Stalk
public import ReasLib.RingTheory.CohenMacaulay.Module.Self
public import ReasLib.Topology.Specialization.Dimension

/-!
# Dimension functions on Cohen–Macaulay schemes

The negative Krull dimension of the local ring defines an integer-valued dimension function on
a Cohen–Macaulay scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.CohenMacaulay

/-- The dimension function of a Cohen–Macaulay scheme is the negative Krull dimension of
the local ring at each point. -/
noncomputable abbrev dimensionFunction (S : Scheme.{u}) [CohenMacaulay S] : S → ℤ :=
  fun s ↦ -(((ringKrullDim (S.presheaf.stalk s)).unbotD 0).toNat : ℤ)

/-- The value of `dimensionFunction S` at `s` is the negative Krull dimension of
`𝒪_{S,s}`. -/
@[simp]
theorem dimensionFunction_apply (S : Scheme.{u}) [CohenMacaulay S] (s : S) :
    dimensionFunction S s =
      -(((ringKrullDim (S.presheaf.stalk s)).unbotD 0).toNat : ℤ) := sorry

/-- The negative local-ring dimension is a dimension function on a Cohen–Macaulay scheme. -/
instance instIsDimensionFunction (S : Scheme.{u}) [CohenMacaulay S] :
    IsDimensionFunction (dimensionFunction S) := sorry

end AlgebraicGeometry.Scheme.CohenMacaulay
