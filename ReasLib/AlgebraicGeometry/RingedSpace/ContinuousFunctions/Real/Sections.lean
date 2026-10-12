/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Continuous functions as structure-module sections

This file connects a continuous map `X → ℝ` to the top-open value of the continuous-function
structure sheaf and then to the corresponding global section of its unit module sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real

/-- A continuous function on `X`, restricted to the top open. -/
noncomputable def topValue (X : TopCat.{u}) (f : C(X, ℝ)) : C((⊤ : Opens X), ℝ) :=
  f.restrict (⊤ : Set X)

/-- Evaluation of `topValue` agrees with evaluation of the original continuous function. -/
@[simp]
theorem topValue_apply (X : TopCat.{u}) (f : C(X, ℝ)) (x : (⊤ : Opens X)) :
    topValue X f x = f x.1 := sorry

/-- A continuous function on `X`, restricted to the top open and viewed as a value of the
continuous-function structure sheaf. -/
@[stacks 01BL "continuous function as a top section"]
noncomputable def topSection (X : TopCat.{u}) (f : C(X, ℝ)) :
    (ringedSpace X).presheaf.obj (op (⊤ : Opens X)) :=
  topValue X f

/-- The structure-sheaf value `topSection` is represented by the concrete continuous map
`topValue`. -/
theorem topSection_eq_topValue (X : TopCat.{u}) (f : C(X, ℝ)) :
    topSection X f = topValue X f := sorry

/-- A continuous real-valued function as a global section of the structure module on
`ringedSpace X`. -/
@[stacks 01BL "continuous function as a unit section"]
noncomputable def unitSection (X : TopCat.{u}) (f : C(X, ℝ)) :
    (SheafOfModules.unit (ringedSpace X).ringCatSheaf).sections :=
  AlgebraicGeometry.RingedSpace.unitSectionFromTop (ringedSpace X) (topSection X f)

/-- Top-open evaluation of `unitSection` recovers the restricted continuous function. -/
@[simp]
theorem sectionsEquivTop_unitSection (X : TopCat.{u}) (f : C(X, ℝ)) :
    AlgebraicGeometry.RingedSpace.sectionsEquivTop
        (SheafOfModules.unit (ringedSpace X).ringCatSheaf) (unitSection X f) =
      topSection X f := sorry

/-- The value of a structure-module section on `U`, viewed as a continuous real-valued function. -/
noncomputable def sectionValue (X : TopCat.{u})
    (s : (SheafOfModules.unit (ringedSpace X).ringCatSheaf).sections)
    (U : Opens X) : C(U, ℝ) :=
  s.val (op U)

/-- On every open set, `unitSection X f` evaluates pointwise as the original continuous
function. -/
@[simp]
theorem unitSection_eval_apply (X : TopCat.{u}) (f : C(X, ℝ))
    (U : Opens X) (x : U) :
    sectionValue X (unitSection X f) U x = f x.1 := sorry

/-- A point is in the sheaf-theoretic support of `unitSection X f` exactly when `f` is not
identically zero on any neighborhood of that point. -/
theorem mem_sectionSupport_unitSection_iff (X : TopCat.{u}) (f : C(X, ℝ)) (x : X) :
    x ∈ SheafOfModules.sectionSupport (unitSection X f) ↔
      {y : X | f y = 0} ∉ 𝓝 x := sorry

end AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real
