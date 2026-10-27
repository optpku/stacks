/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

open CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.Crystalline.Base

/-- The relative crystalline category of a prime-local divided-power base has all finite
nonempty limits, including binary products and pullbacks. -/
theorem hasFiniteNonemptyLimits {p : ℕ} [Fact p.Prime] (B : Base.{u} p) :
    HasFiniteNonemptyLimits
      (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed) := sorry

/-- The source-forgetting functor of a prime-local relative crystalline category preserves
all existing limits of arbitrary diagram size. -/
theorem forgetful_preservesLimits {p : ℕ} [Fact p.Prime] (B : Base.{u} p) :
    PreservesLimitsOfSize.{v, w}
      (crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Base
