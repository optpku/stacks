/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-! # Finite presentation and relative flatness of invertible modules -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- A tensor-invertible module on an algebraic space is finitely presented. -/
theorem isFinitePresentationOfIsInvertible {Y : AlgebraicSpace S}
    (L : Y.Modules) (h : isInvertibleObject L) : L.IsFinitePresentation := sorry

/-- Tensor-invertible modules are finitely presented. -/
instance instIsFinitePresentationOfIsInvertible {Y : AlgebraicSpace S}
    (L : Y.Modules) [isInvertibleObject L] : L.IsFinitePresentation :=
  isFinitePresentationOfIsInvertible L inferInstance

/-- A tensor-invertible module is relatively flat along a flat morphism. -/
theorem flatOverOfIsInvertible {Y Z : AlgebraicSpace S} (L : Y.Modules)
    (g : Y ⟶ Z) (hL : isInvertibleObject L) (hg : Flat g) :
    flatOver L g := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
