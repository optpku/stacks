/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.IrreducibleComponents
import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible components of fibres of finite-presentation morphisms

This file records local constructibility of the finite level sets of the geometric
irreducible-fibre component count.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- For a finite-presentation morphism, every finite level set of the geometric
irreducible-fibre component count is locally constructible. -/
@[stacks 055B]
theorem geometricIrreducibleFiberComponentCount_levelSet_isLocallyConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f] (n : ℕ) :
    Topology.IsLocallyConstructible
      {y : Y | f.geometricIrreducibleFiberComponentCount y = n} := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
