/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree

/-- A binary biproduct of vector bundles in a common cohomological degree, with
pointwise ranks strictly less than `p` and `q`, has pointwise rank strictly less
than `p + q` in that degree. -/
theorem biprod {X : Scheme.{u}}
    {E F : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace} {i : ℤ} {p q : ℕ}
    (hE : IsVectorBundleOfRankLTInDegree E i p)
    (hF : IsVectorBundleOfRankLTInDegree F i q) :
    IsVectorBundleOfRankLTInDegree (E ⊞ F) i (p + q) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
