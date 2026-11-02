/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.ResidueField

/-!
# Families of cycles on fibres

This file defines the type of a family of cycles of fixed dimension on the
scheme-theoretic fibres of a morphism, together with the fibrewise relative
dimension function obtained from the residue-field structure morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The dimension function on a scheme-theoretic fibre, obtained by pulling back the
constant-zero dimension function along the morphism to `Spec κ(s)`. -/
noncomputable abbrev fiberRelativeDimensionFunction
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) : f.fiber s → ℤ :=
  (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0)

/-- On a fibre, the relative dimension function is the residue-field transcendence degree. -/
theorem fiberRelativeDimensionFunction_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (x : f.fiber s) :
    f.fiberRelativeDimensionFunction s x =
      ((f.fiberToSpecResidueField s).residueFieldTrdegAt x : ℤ) := sorry

/-- A family of `k`-cycles on the scheme-theoretic fibres of `f : X ⟶ S`. -/
abbrev FiberCycleFamily {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) : Type u :=
  (s : S) → CycleGroup (f.fiber s) (f.fiberRelativeDimensionFunction s) k

/-- Unfolding the type of a family of cycles on fibres. -/
theorem FiberCycleFamily_def {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    f.FiberCycleFamily k =
      ((s : S) → CycleGroup (f.fiber s) (f.fiberRelativeDimensionFunction s) k) := sorry

end AlgebraicGeometry.Scheme.Hom
