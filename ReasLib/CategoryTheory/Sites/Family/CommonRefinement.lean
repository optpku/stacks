/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Covering
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Common refinements of covering families

Two covering families on a precoverage with pullbacks admit a common covering refinement.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]
variable {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
  [J.IsStableUnderComposition]

/-- Two covering families over `U` admit a common covering refinement. -/
theorem exists_covering_common_refinement {U : C}
    (𝒰 𝒱 : Over.{w} U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ (𝒲 : Over.{w} U) (_ : IsCovering J 𝒲), Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := sorry

end SemiRepresentableFamily.Over
end CategoryTheory
