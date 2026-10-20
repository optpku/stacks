/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Fibre degrees of finite locally free morphisms

This file records uniform bounds on the fibre degrees of finite locally free
scheme morphisms of fixed rank.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A finite locally free morphism of rank `d` has fibre degrees bounded by `d`. -/
theorem degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank
    (f : X ⟶ Y) (d : ℕ) [IsFiniteLocallyFreeOfRank f d] :
    degreesOfFibresBoundedBy f d := sorry

/-- A finite locally free morphism of fixed rank has universally bounded fibres. -/
theorem universallyBoundedFibres_of_isFiniteLocallyFreeOfRank
    (f : X ⟶ Y) (d : ℕ) [IsFiniteLocallyFreeOfRank f d] :
    universallyBoundedFibres f :=
  ⟨d, degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank f d⟩

end Scheme.Hom
end AlgebraicGeometry
