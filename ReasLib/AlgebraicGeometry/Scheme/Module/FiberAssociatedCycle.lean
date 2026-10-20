/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-`r` associated cycle of a coherent module after pullback to a
scheme-theoretic fibre. -/
noncomputable def fiberAssociatedCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] :
    CycleGroup (f.fiber s) (f.fiberDimensionFunction s) r :=
  ⟨associatedCycle ((pullback (f.fiberι s)).obj F) (f.fiberDimensionFunction s) r,
    associatedCycle_mem_dimensionSubgroup
      ((pullback (f.fiberι s)).obj F) (f.fiberDimensionFunction s) r⟩

/-- Forgetting the grading of a fibre associated cycle recovers the associated algebraic
cycle of the pulled-back module. -/
theorem fiberAssociatedCycle_toAlgebraicCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s) :
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x := rfl

/-- Coefficients of the fibre associated cycle agree with the pulled-back module cycle. -/
theorem fiberAssociatedCycle_apply {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s) :
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x := rfl

end AlgebraicGeometry.Scheme.Modules
