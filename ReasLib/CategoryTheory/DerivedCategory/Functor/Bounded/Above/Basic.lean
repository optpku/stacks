/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The bounded-above induced derived functor

@stack 05T4

This leaf records computation, shift, and triangulated API for the canonical functor
`K⁻(𝒜) ⥤ D⁻(ℬ)` induced by an additive functor `𝒜 ⥤ ℬ`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

/-- The functor `K⁻(𝒜) ⥤ D⁻(ℬ)` induced by an additive functor. -/
@[stacks 05T4]
def toBoundedAboveDerived (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.Minus 𝒜 ⥤ DerivedCategory.Minus ℬ :=
  F.mapHomotopyCategoryMinus ⋙ DerivedCategory.Minus.Qh ℬ

namespace toBoundedAboveDerived

/-- Objectwise computation for the bounded-above derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded-above derived functor computation"]
theorem obj (F : 𝒜 ⥤ ℬ) [F.Additive] (X : HomotopyCategory.Minus 𝒜) :
    F.toBoundedAboveDerived.obj X =
      (DerivedCategory.Minus.Qh ℬ).obj (F.mapHomotopyCategoryMinus.obj X) := sorry

/-- Morphismwise computation for the bounded-above derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded-above derived functor computation"]
theorem map (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Minus 𝒜} (f : X ⟶ Y) :
    F.toBoundedAboveDerived.map f =
      (DerivedCategory.Minus.Qh ℬ).map (F.mapHomotopyCategoryMinus.map f) := sorry

/-- The bounded-above derived functor induced by `F` commutes with cohomological shifts. -/
@[stacks 05T4]
noncomputable instance commShift (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedAboveDerived.CommShift ℤ := by
  dsimp only [toBoundedAboveDerived]
  infer_instance

/-- The bounded-above derived functor induced by `F` is triangulated. -/
@[stacks 05T4]
instance isTriangulated (F : 𝒜 ⥤ ℬ) [F.Additive]
    [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    F.toBoundedAboveDerived.IsTriangulated := sorry


end toBoundedAboveDerived

end CategoryTheory.Functor
