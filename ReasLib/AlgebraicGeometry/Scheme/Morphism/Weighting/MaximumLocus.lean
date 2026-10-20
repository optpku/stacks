/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Semicontinuity
import Mathlib.Topology.Semicontinuity.Basic
import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood

/-!
# The maximum locus of a positive weighting
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus where the fibre integral of a positive weighting attains a specified greatest
value is open. -/
theorem IsWeighting.isOpen_fiberIntegralMaximumLocus
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) (d : ℤ)
    (h_max : IsGreatest (Set.range (f.fiberIntegral hf w)) d) :
    IsOpen {y : Y | f.fiberIntegral hf w y = d} := sorry

/-- The open locus where the fibre integral of a positive weighting attains a specified
greatest value. -/
noncomputable def IsWeighting.fiberIntegralMaximumLocus
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) (d : ℤ)
    (h_max : IsGreatest (Set.range (f.fiberIntegral hf w)) d) : Y.Opens :=
  ⟨{y : Y | f.fiberIntegral hf w y = d},
    hw.isOpen_fiberIntegralMaximumLocus h_pos d h_max⟩

/-- A point belongs to the fibre-integral maximum locus exactly when its fibre integral is the
specified greatest value. -/
theorem IsWeighting.mem_fiberIntegralMaximumLocus
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) (d : ℤ)
    (h_max : IsGreatest (Set.range (f.fiberIntegral hf w)) d) (y : Y) :
    y ∈ hw.fiberIntegralMaximumLocus h_pos d h_max ↔
      f.fiberIntegral hf w y = d := sorry

/-- A separated locally quasi-finite morphism with a positive weighting is finite over the
locus where its fibre integral attains a greatest value. -/
theorem IsWeighting.isFinite_restrict_maximumLocus
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) (d : ℤ)
    (h_max : IsGreatest (Set.range (f.fiberIntegral hf w)) d) :
    IsFinite (f ∣_ hw.fiberIntegralMaximumLocus h_pos d h_max) := sorry

end AlgebraicGeometry.Scheme.Hom
