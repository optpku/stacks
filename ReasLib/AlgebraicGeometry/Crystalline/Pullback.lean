/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Base

/-- A pullback square of relative crystalline objects induces a pullback square of
thickening schemes when the right thickening map is flat and its source-inclusion
square is cartesian. -/
theorem thickening_isPullback_of_flat {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    {c₁ c₂ c₃ c :
      RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed}
    (top : c₃ ⟶ c₂) (left : c₃ ⟶ c₁) (bottom : c₁ ⟶ c) (right : c₂ ⟶ c)
    (h_square : IsPullback left top bottom right) [Flat right.thickening]
    (h_source : IsPullback right.source.left c₂.1.inclusion c.1.inclusion right.thickening) :
    IsPullback left.thickening top.thickening bottom.thickening right.thickening := sorry

end AlgebraicGeometry.Scheme.Crystalline.Base
