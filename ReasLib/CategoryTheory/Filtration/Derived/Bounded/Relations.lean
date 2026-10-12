/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relations between bounded finite filtered derived categories

The three boundedness presentations are full subcategories of the same finite filtered derived
category.  This leaf owns their membership characterizations and canonical inclusion functors;
the underlying bounded properties remain in `Derived.Bounded`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Bounded

/-- The bounded property is the intersection of the bounded-below and bounded-above properties. -/
@[stacks 05S4 "bounded finite filtered derived category"]
theorem property_eq_inf :
    property C h_inverts = Plus.property C h_inverts ⊓ Minus.property C h_inverts := sorry

end Bounded

namespace Bounded.canonicalProperty

/-- The canonical bounded property is the intersection of the canonical bounded-below and
bounded-above properties. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
theorem eq_inf :
    Bounded.canonicalProperty C =
      Plus.canonicalProperty C ⊓ Minus.canonicalProperty C := sorry

/-- Membership in the canonical bounded finite filtered derived category is characterized by
two-sided vanishing of the canonical associated-graded cohomology. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    Bounded.canonicalProperty C X ↔
      (∃ a : ℤ, ∀ i < a,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.canonicalLift C).obj X))) ∧
      (∃ b : ℤ, ∀ i > b,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.canonicalLift C).obj X))) := sorry

end Bounded.canonicalProperty

namespace Plus

/-- Membership in the bounded-below finite filtered derived category is characterized by
vanishing of sufficiently low associated-graded cohomology. -/
@[stacks 05S4 "bounded below finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    property C h_inverts X ↔
      ∃ n : ℤ, ∀ i < n,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.lift C h_inverts).obj X)) := sorry

/-- The ambient inclusion of bounded-below finite filtered derived objects. -/
@[stacks 05S4 "bounded below finite filtered derived category"]
noncomputable def inclusion : Category C h_inverts ⥤ Quotient.Category C :=
  (property C h_inverts).ι

end Plus

namespace Plus.canonicalProperty

/-- Membership in the canonical bounded-below finite filtered derived category is characterized
by vanishing of sufficiently low associated-graded cohomology. -/
@[stacks 05S4 "canonical bounded below finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    Plus.canonicalProperty C X ↔
      ∃ n : ℤ, ∀ i < n,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.canonicalLift C).obj X)) := sorry

end Plus.canonicalProperty

namespace Plus

/-- The ambient inclusion of the canonical bounded-below finite filtered derived category. -/
@[stacks 05S4 "canonical bounded below finite filtered derived category"]
noncomputable abbrev canonicalInclusion :
    canonicalCategory C ⥤ Quotient.Category C :=
  inclusion C (AssociatedGraded.inverts C)

end Plus

namespace Minus

/-- Membership in the bounded-above finite filtered derived category is characterized by
vanishing of sufficiently high associated-graded cohomology. -/
@[stacks 05S4 "bounded above finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    property C h_inverts X ↔
      ∃ n : ℤ, ∀ i > n,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.lift C h_inverts).obj X)) := sorry

/-- The ambient inclusion of bounded-above finite filtered derived objects. -/
@[stacks 05S4 "bounded above finite filtered derived category"]
noncomputable def inclusion : Category C h_inverts ⥤ Quotient.Category C :=
  (property C h_inverts).ι

end Minus

namespace Minus.canonicalProperty

/-- Membership in the canonical bounded-above finite filtered derived category is characterized
by vanishing of sufficiently high associated-graded cohomology. -/
@[stacks 05S4 "canonical bounded above finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    Minus.canonicalProperty C X ↔
      ∃ n : ℤ, ∀ i > n,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.canonicalLift C).obj X)) := sorry

end Minus.canonicalProperty

namespace Minus

/-- The ambient inclusion of the canonical bounded-above finite filtered derived category. -/
@[stacks 05S4 "canonical bounded above finite filtered derived category"]
noncomputable abbrev canonicalInclusion :
    canonicalCategory C ⥤ Quotient.Category C :=
  inclusion C (AssociatedGraded.inverts C)

end Minus

namespace Bounded

/-- Membership in the bounded finite filtered derived category is characterized by two-sided
vanishing of associated-graded cohomology. -/
@[stacks 05S4 "bounded finite filtered derived category"]
theorem mem_iff (X : Quotient.Category C) :
    property C h_inverts X ↔
      (∃ a : ℤ, ∀ i < a,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.lift C h_inverts).obj X))) ∧
      (∃ b : ℤ, ∀ i > b,
        IsZero ((DerivedCategory.homologyFunctor (GradedObject ℤ C) i).obj
          ((AssociatedGraded.lift C h_inverts).obj X))) := sorry

/-- The ambient inclusion of bounded finite filtered derived objects. -/
@[stacks 05S4 "bounded finite filtered derived category"]
noncomputable def inclusion : Category C h_inverts ⥤ Quotient.Category C :=
  (property C h_inverts).ι

/-- The ambient inclusion of the canonical bounded finite filtered derived category. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
noncomputable abbrev canonicalInclusion :
    canonicalCategory C ⥤ Quotient.Category C :=
  inclusion C (AssociatedGraded.inverts C)

namespace ToPlus

/-- The canonical inclusion from the bounded finite filtered derived category to its
bounded-below part. -/
@[stacks 05S4 "bounded finite filtered derived category"]
noncomputable def inclusion :
    Category C h_inverts ⥤ Plus.Category C h_inverts :=
  ObjectProperty.ιOfLE (fun _ hX ↦ hX.1)

/-- The bounded-to-plus inclusion followed by the ambient inclusion is the bounded ambient
inclusion. -/
@[stacks 05S4 "bounded finite filtered derived category"]
noncomputable def compInclusionIso :
    inclusion C h_inverts ⋙ Plus.inclusion C h_inverts ≅ Bounded.inclusion C h_inverts :=
  ObjectProperty.ιOfLECompιIso (fun _ hX ↦ hX.1)

/-- The canonical inclusion from the canonical bounded category to its bounded-below part. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
noncomputable abbrev canonicalInclusion :
    Bounded.canonicalCategory C ⥤ Plus.canonicalCategory C :=
  inclusion C (AssociatedGraded.inverts C)

/-- The canonical bounded-to-plus inclusion followed by the ambient inclusion is the canonical
bounded ambient inclusion. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
noncomputable abbrev canonicalCompInclusionIso :
    canonicalInclusion C ⋙ Plus.canonicalInclusion C ≅ Bounded.canonicalInclusion C :=
  compInclusionIso C (AssociatedGraded.inverts C)

end ToPlus

namespace ToMinus

/-- The canonical inclusion from the bounded finite filtered derived category to its
bounded-above part. -/
@[stacks 05S4 "bounded finite filtered derived category"]
noncomputable def inclusion :
    Category C h_inverts ⥤ Minus.Category C h_inverts :=
  ObjectProperty.ιOfLE (fun _ hX ↦ hX.2)

/-- The bounded-to-minus inclusion followed by the ambient inclusion is the bounded ambient
inclusion. -/
@[stacks 05S4 "bounded finite filtered derived category"]
noncomputable def compInclusionIso :
    inclusion C h_inverts ⋙ Minus.inclusion C h_inverts ≅ Bounded.inclusion C h_inverts :=
  ObjectProperty.ιOfLECompιIso (fun _ hX ↦ hX.2)

/-- The canonical inclusion from the canonical bounded category to its bounded-above part. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
noncomputable abbrev canonicalInclusion :
    Bounded.canonicalCategory C ⥤ Minus.canonicalCategory C :=
  inclusion C (AssociatedGraded.inverts C)

/-- The canonical bounded-to-minus inclusion followed by the ambient inclusion is the canonical
bounded ambient inclusion. -/
@[stacks 05S4 "canonical bounded finite filtered derived category"]
noncomputable abbrev canonicalCompInclusionIso :
    canonicalInclusion C ⋙ Minus.canonicalInclusion C ≅ Bounded.canonicalInclusion C :=
  compInclusionIso C (AssociatedGraded.inverts C)

end ToMinus

end Bounded

end CategoryTheory.FilteredObject.FiniteDerived
