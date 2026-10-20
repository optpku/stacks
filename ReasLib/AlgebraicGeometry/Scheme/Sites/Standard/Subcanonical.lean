/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

@[expose] public section

universe u

namespace AlgebraicGeometry.StandardTopology

/-- The topology on `Over S` attached to any standard topology is subcanonical. -/
instance overTopologySubcanonical (τ : StandardTopology) (S : Scheme.{u}) :
    (τ.overTopology S).Subcanonical := sorry

end AlgebraicGeometry.StandardTopology
