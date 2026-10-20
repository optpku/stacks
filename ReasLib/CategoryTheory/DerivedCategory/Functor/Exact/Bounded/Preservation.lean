module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.TStructure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preservation of canonical t-structure bounds by exact functors

An exact functor between abelian categories preserves every fixed lower and
upper bound for the canonical t-structures on their derived categories.  The
named theorems form the explicit API, while the corresponding instances let
bounded restrictions reuse the same facts without local instance plumbing.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- An exact functor preserves every fixed lower bound for the canonical
t-structures on derived categories. -/
@[stacks 015F "exact derived functors preserve lower t-structure bounds"]
theorem isGE (F : A ⥤ₑ B) (K : DerivedCategory A) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n := sorry

/-- An exact functor preserves every fixed upper bound for the canonical
t-structures on derived categories. -/
@[stacks 015F "exact derived functors preserve upper t-structure bounds"]
theorem isLE (F : A ⥤ₑ B) (K : DerivedCategory A) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n := sorry

/-- The image of a lower-bounded derived object under an exact functor carries
the same lower bound canonically. -/
instance obj_isGE (F : A ⥤ₑ B) (K : DerivedCategory A) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n :=
  isGE F K n

/-- The image of an upper-bounded derived object under an exact functor carries
the same upper bound canonically. -/
instance obj_isLE (F : A ⥤ₑ B) (K : DerivedCategory A) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n :=
  isLE F K n

namespace Plus

/-- An exact derived functor carries the bounded-below object property into
the bounded-below object property. -/
@[stacks 015F "exact derived functors preserve the bounded-below property"]
theorem mapsTo (F : A ⥤ₑ B) :
    (t.plus : ObjectProperty (DerivedCategory A)) ≤
      (t.plus : ObjectProperty (DerivedCategory B)).inverseImage
        F.mapDerivedCategory := sorry

end Plus

namespace Minus

/-- An exact derived functor carries the bounded-above object property into
the bounded-above object property. -/
@[stacks 015F "exact derived functors preserve the bounded-above property"]
theorem mapsTo (F : A ⥤ₑ B) :
    (t.minus : ObjectProperty (DerivedCategory A)) ≤
      (t.minus : ObjectProperty (DerivedCategory B)).inverseImage
        F.mapDerivedCategory := sorry

end Minus

namespace Bounded

/-- An exact derived functor carries the bounded object property into the
bounded object property. -/
@[stacks 015F "exact derived functors preserve the bounded property"]
theorem mapsTo (F : A ⥤ₑ B) :
    (t.bounded : ObjectProperty (DerivedCategory A)) ≤
      (t.bounded : ObjectProperty (DerivedCategory B)).inverseImage
        F.mapDerivedCategory := sorry

end Bounded

end CategoryTheory.ExactFunctor.Derived
