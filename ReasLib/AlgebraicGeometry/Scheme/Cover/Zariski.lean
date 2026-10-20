/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/-- A family of scheme morphisms is a Zariski precover exactly when every map is an open
immersion and the ranges of the maps cover the target scheme. -/
theorem ofArrows_mem_zariskiPrecoverage_iff
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    Presieve.ofArrows X f ∈ zariskiPrecoverage T ↔
      (∀ i, IsOpenImmersion (f i)) ∧ (⋃ i, Set.range (f i)) = Set.univ := sorry

end AlgebraicGeometry.Scheme
