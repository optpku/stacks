/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.SheafDerivation
import StacksCheckRecall

open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
  (F : SheafOfModules.{u} (smallStructureSheaf (S := B.scheme) (I := B.ideal)
    (γ := B.dividedPowers) (h_compatible := B.compatible)
    (X := B.source) (x₀ := B.sourceToClosed)))

/- Definition 60.12.1: in Situation 60.7.5, an `S`-derivation of the crystalline
structure sheaf into a sheaf of modules on the small crystalline site is a natural
additive Leibniz map, vanishing on factoring base opens and respecting divided powers. -/
@[stacks 07IX] #check (AlgebraicGeometry.Scheme.Crystalline.SDerivation B F : Type (u + 1))
