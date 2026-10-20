/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computation for Bounded Finite Filtered Localizations

The bounded-below, bounded-above, and bounded quotient functors are lifts
through full subcategories.  This leaf exposes their object, morphism, and
inclusion-comparison normal forms without unfolding `ObjectProperty.lift`.
-/

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.Quotient.functor

/-- The underlying object of the bounded-below quotient is its ambient finite
filtered derived quotient image. -/
@[simp, stacks 05S6 "bounded-below filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    ((Plus.Quotient.functor C h_inverts).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the bounded-below quotient is its ambient
finite filtered derived quotient map. -/
@[simp, stacks 05S6 "bounded-below filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Plus.Quotient.functor C h_inverts).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Plus.Quotient.functor

namespace Plus.Quotient.compInclusionIso

/-- The forward bounded-below inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded-below filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Quotient.compInclusionIso C h_inverts).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-below inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded-below filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Quotient.compInclusionIso C h_inverts).inv.app X = 𝟙 _ := sorry

end Plus.Quotient.compInclusionIso

namespace Plus.Quotient.canonicalFunctor

/-- The underlying object of the canonical bounded-below quotient is its ambient finite
filtered derived quotient image. -/
@[simp, stacks 05S6 "canonical bounded-below filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    ((Plus.Quotient.canonicalFunctor C).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the canonical bounded-below quotient is its ambient finite
filtered derived quotient map. -/
@[simp, stacks 05S6 "canonical bounded-below filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Plus.Quotient.canonicalFunctor C).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Plus.Quotient.canonicalFunctor

namespace Plus.Quotient.canonicalCompInclusionIso

/-- The forward canonical bounded-below inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded-below filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Quotient.canonicalCompInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse canonical bounded-below inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded-below filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Quotient.canonicalCompInclusionIso C).inv.app X = 𝟙 _ := sorry

end Plus.Quotient.canonicalCompInclusionIso

namespace Minus.Quotient.functor

/-- The underlying object of the bounded-above quotient is its ambient finite
filtered derived quotient image. -/
@[simp, stacks 05S6 "bounded-above filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    ((Minus.Quotient.functor C h_inverts).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the bounded-above quotient is its ambient
finite filtered derived quotient map. -/
@[simp, stacks 05S6 "bounded-above filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Minus.Quotient.functor C h_inverts).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Minus.Quotient.functor

namespace Minus.Quotient.compInclusionIso

/-- The forward bounded-above inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded-above filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Quotient.compInclusionIso C h_inverts).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-above inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded-above filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Quotient.compInclusionIso C h_inverts).inv.app X = 𝟙 _ := sorry

end Minus.Quotient.compInclusionIso

namespace Minus.Quotient.canonicalFunctor

/-- The underlying object of the canonical bounded-above quotient is its ambient finite
filtered derived quotient image. -/
@[simp, stacks 05S6 "canonical bounded-above filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    ((Minus.Quotient.canonicalFunctor C).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the canonical bounded-above quotient is its ambient finite
filtered derived quotient map. -/
@[simp, stacks 05S6 "canonical bounded-above filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Minus.Quotient.canonicalFunctor C).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Minus.Quotient.canonicalFunctor

namespace Minus.Quotient.canonicalCompInclusionIso

/-- The forward canonical bounded-above inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded-above filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Quotient.canonicalCompInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse canonical bounded-above inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded-above filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Quotient.canonicalCompInclusionIso C).inv.app X = 𝟙 _ := sorry

end Minus.Quotient.canonicalCompInclusionIso

namespace Bounded.Quotient.functor

/-- The underlying object of the bounded quotient is its ambient finite
filtered derived quotient image. -/
@[simp, stacks 05S6 "bounded filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    ((Bounded.Quotient.functor C h_inverts).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the bounded quotient is its ambient finite
filtered derived quotient map. -/
@[simp, stacks 05S6 "bounded filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Bounded.Quotient.functor C h_inverts).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Bounded.Quotient.functor

namespace Bounded.Quotient.compInclusionIso

/-- The forward bounded inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Quotient.compInclusionIso C h_inverts).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded inclusion comparison has identity components. -/
@[simp, stacks 05S6 "bounded filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Quotient.compInclusionIso C h_inverts).inv.app X = 𝟙 _ := sorry

end Bounded.Quotient.compInclusionIso

namespace Bounded.Quotient.canonicalFunctor

/-- The underlying object of the canonical bounded quotient is its ambient finite filtered
derived quotient image. -/
@[simp, stacks 05S6 "canonical bounded filtered quotient object computation"]
theorem obj_obj (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    ((Bounded.Quotient.canonicalFunctor C).obj X).obj =
      (FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj := sorry

/-- The underlying morphism of the canonical bounded quotient is its ambient finite filtered
derived quotient map. -/
@[simp, stacks 05S6 "canonical bounded filtered quotient map computation"]
theorem map_hom {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)}
    (f : X ⟶ Y) :
    ((Bounded.Quotient.canonicalFunctor C).map f).hom =
      (FilteredObject.FiniteDerived.Quotient.functor C).map f.hom := sorry

end Bounded.Quotient.canonicalFunctor

namespace Bounded.Quotient.canonicalCompInclusionIso

/-- The forward canonical bounded inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded filtered quotient inclusion computation"]
theorem hom_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Quotient.canonicalCompInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse canonical bounded inclusion comparison has identity components. -/
@[simp, stacks 05S6 "canonical bounded filtered quotient inclusion computation"]
theorem inv_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Quotient.canonicalCompInclusionIso C).inv.app X = 𝟙 _ := sorry

end Bounded.Quotient.canonicalCompInclusionIso

end CategoryTheory.FilteredObject.FiniteDerived
