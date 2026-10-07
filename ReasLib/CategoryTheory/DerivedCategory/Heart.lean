module

public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Canonical Heart of a Derived Category

The canonical `t`-structure on `DerivedCategory 𝒜` has heart `𝒜`, embedded by
the degree-zero `singleFunctor`.  The essential-image equality is the only
proof debt in the instance; its functor, fullness, faithfulness, and additive
structure are the canonical Mathlib data.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe w v u

noncomputable section

namespace CategoryTheory.DerivedCategory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The essential image of the degree-zero `singleFunctor` is the heart of the
canonical `t`-structure on the derived category. -/
@[stacks 08J5]
theorem singleFunctor_essImage_eq_heart :
    (DerivedCategory.singleFunctor 𝒜 0).essImage =
      (t : Triangulated.TStructure (DerivedCategory 𝒜)).heart := sorry

/-- The abelian category is the canonical heart of its derived category,
embedded by the degree-zero `singleFunctor`. -/
@[stacks 08J5]
noncomputable instance canonicalHeart :
    (t : Triangulated.TStructure (DerivedCategory 𝒜)).Heart 𝒜 where
  ι := DerivedCategory.singleFunctor 𝒜 0
  essImage_eq_heart := singleFunctor_essImage_eq_heart 𝒜

end CategoryTheory.DerivedCategory

end
