module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The two-sided bounded induced derived functor

This leaf records computation, shift, and triangulated API for the canonical functor
`Kᵇ(𝒜) ⥤ Dᵇ(ℬ)` induced by an additive functor `𝒜 ⥤ ℬ`.
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

/-- The functor `Kᵇ(𝒜) ⥤ Dᵇ(ℬ)` induced by an additive functor. -/
@[stacks 05T4]
def toBoundedDerived (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.Bounded 𝒜 ⥤ DerivedCategory.Bounded ℬ :=
  F.mapHomotopyCategoryBounded ⋙ DerivedCategory.Bounded.Qh ℬ

namespace toBoundedDerived

/-- Objectwise computation for the bounded derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded derived functor computation"]
theorem obj (F : 𝒜 ⥤ ℬ) [F.Additive] (X : HomotopyCategory.Bounded 𝒜) :
    F.toBoundedDerived.obj X =
      (DerivedCategory.Bounded.Qh ℬ).obj (F.mapHomotopyCategoryBounded.obj X) := sorry

/-- Morphismwise computation for the bounded derived functor induced by `F`. -/
@[simp, stacks 05T4 "bounded derived functor computation"]
theorem map (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : HomotopyCategory.Bounded 𝒜} (f : X ⟶ Y) :
    F.toBoundedDerived.map f =
      (DerivedCategory.Bounded.Qh ℬ).map (F.mapHomotopyCategoryBounded.map f) := sorry

/-- The bounded derived functor induced by `F` commutes with cohomological shifts. -/
@[stacks 05T4]
noncomputable instance commShift (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.toBoundedDerived.CommShift ℤ := by
  dsimp only [toBoundedDerived]
  infer_instance

/-- The bounded derived functor induced by `F` is triangulated. -/
@[stacks 05T4]
instance isTriangulated (F : 𝒜 ⥤ ℬ) [F.Additive]
    [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    F.toBoundedDerived.IsTriangulated := sorry


end toBoundedDerived

end CategoryTheory.Functor
