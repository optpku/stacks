/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite separable extensions in the valuative criterion

The existence part of the valuative criterion for a morphism of algebraic spaces
is equivalent to requiring dominating extensions with finite separable
fraction-field extension.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCriterion.Existence

/-- A morphism of algebraic spaces satisfies the existence part of the valuative
criterion if and only if every valuative square admits a dominating extension
with finite separable fraction-field extension. -/
theorem iff_exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f,
      ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' :=
  sorry

/-- If every valuative square admits a dominating extension with finite
separable fraction-field extension, then `f` satisfies the existence part of
the valuative criterion. -/
theorem of_exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ sq : ValuativeCommSq f,
      ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K') :
    Existence f :=
  (iff_exists_finiteSeparable f).mpr h

/-- If `f` satisfies the existence part of the valuative criterion, then every
valuative square admits a dominating extension whose fraction-field extension
is finite separable. -/
theorem exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Existence f] (sq : ValuativeCommSq f) :
    ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' :=
  (iff_exists_finiteSeparable f).mp inferInstance sq

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicSpace
