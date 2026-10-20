/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-! The canonical public owner supplies universal homeomorphisms and the
characterization of the topology on algebraic-space points. -/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
