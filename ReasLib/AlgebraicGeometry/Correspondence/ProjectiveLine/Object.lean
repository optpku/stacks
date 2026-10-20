/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Category
public import ReasLib.AlgebraicGeometry.Correspondence.ProjectiveLine

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.ProjectiveLine

variable {k : Type u} [Field k]

/-- The projective line as an object of the degree-zero correspondence category. -/
abbrev asObject (k : Type u) [Field k] : Category k :=
  ⟨ProjectiveSpace.schemeOver k 1, ⟨inferInstance, inferInstance⟩⟩

/-- The scheme underlying the degree-zero correspondence object `asObject k` is `ℙ¹_k`. -/
theorem asObject_scheme (k : Type u) [Field k] :
    (asObject k).scheme = ProjectiveSpace.schemeOver k 1 := sorry

/-- The correspondence `timesPoint x` is an idempotent endomorphism of `asObject k`. -/
theorem timesPoint_comp_self
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let c₂ : asObject k ⟶ asObject k := timesPoint x
    c₂ ≫ c₂ = c₂ := sorry

end AlgebraicGeometry.Correspondence.ProjectiveLine
