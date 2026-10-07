module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import ReasLib.CategoryTheory.Filtration.Derived.Bounded.Triangulated
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedQuasiIso.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated bounded finite filtered localizations

The bounded quotient functors inherit their shift and triangulated structures from the ambient
finite filtered quotient and the corresponding full-subcategory properties.  This leaf keeps those
instances separate from the localization data and makes the three bounded variants uniform.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.Quotient

/-- The bounded-below quotient functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
noncomputable instance commShift :
    (functor C h_inverts).CommShift ℤ :=
  Functor.CommShift.ofComp (compInclusionIso C h_inverts) ℤ

/-- The bounded-below quotient functor is triangulated. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
instance isTriangulated :
    (functor C h_inverts).IsTriangulated := sorry

end Plus.Quotient

namespace Minus.Quotient

/-- The bounded-above quotient functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
noncomputable instance commShift :
    (functor C h_inverts).CommShift ℤ :=
  Functor.CommShift.ofComp (compInclusionIso C h_inverts) ℤ

/-- The bounded-above quotient functor is triangulated. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
instance isTriangulated :
    (functor C h_inverts).IsTriangulated := sorry

end Minus.Quotient

namespace Bounded.Quotient

/-- The bounded quotient functor commutes with integer shifts. -/
@[stacks 05S6 "bounded finite filtered localization"]
noncomputable instance commShift :
    (functor C h_inverts).CommShift ℤ :=
  Functor.CommShift.ofComp (compInclusionIso C h_inverts) ℤ

/-- The bounded quotient functor is triangulated. -/
@[stacks 05S6 "bounded finite filtered localization"]
instance isTriangulated :
    (functor C h_inverts).IsTriangulated := sorry

end Bounded.Quotient

end CategoryTheory.FilteredObject.FiniteDerived
