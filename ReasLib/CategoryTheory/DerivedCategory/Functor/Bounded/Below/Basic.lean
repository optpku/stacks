module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The bounded-below induced derived functor

@stack 05T4

This leaf records computation, shift, and triangulated API for the canonical functor
`K⁺(𝒜) ⥤ D⁺(ℬ)` induced by an additive functor `𝒜 ⥤ ℬ`.
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

/-- The functor `K⁺(𝒜) ⥤ D⁺(ℬ)` induced by an additive functor. -/
@[stacks 05T4]
abbrev toBoundedBelowDerived (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ :=
  F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

namespace toBoundedBelowDerived

/-- Objectwise computation for the bounded-below derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded-below derived functor computation"]
theorem obj (F : 𝒜 ⥤ ℬ) [F.Additive] (X : HomotopyCategory.Plus 𝒜) :
    F.toBoundedBelowDerived.obj X =
      DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj X) := sorry

/-- Morphismwise computation for the bounded-below derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded-below derived functor computation"]
theorem map (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Plus 𝒜} (f : X ⟶ Y) :
    F.toBoundedBelowDerived.map f =
      DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map f) := sorry

/-- The bounded-below derived functor induced by `F` commutes with cohomological shifts. -/
@[stacks 05T4]
noncomputable instance commShift (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedBelowDerived.CommShift ℤ := by
  dsimp only [toBoundedBelowDerived]
  infer_instance

/-- The bounded-below derived functor induced by `F` is triangulated. -/
@[stacks 05T4]
instance isTriangulated (F : 𝒜 ⥤ ℬ) [F.Additive]
    [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    F.toBoundedBelowDerived.IsTriangulated := sorry


end toBoundedBelowDerived

end CategoryTheory.Functor
