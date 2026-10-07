module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Comparison

/-!
# Components of bounded associated-graded comparisons

The bounded associated-graded functors become the ambient associated-graded
functor after the canonical inclusions.  This leaf exposes identity components
and naturality without unfolding the generic bounded-derived comparison.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

namespace Plus.AssociatedGraded.compInclusionIso

/-- The forward bounded-below associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.AssociatedGraded.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-below associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.AssociatedGraded.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map ((Plus.AssociatedGraded.homotopy C).map f) ≫
        (Plus.AssociatedGraded.compInclusionIso C).hom.app Y =
      (Plus.AssociatedGraded.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Plus.AssociatedGraded.compInclusionIso C).inv.app Y =
      (Plus.AssociatedGraded.compInclusionIso C).inv.app X ≫
        DerivedCategory.Plus.ι.map ((Plus.AssociatedGraded.homotopy C).map f) := sorry

end Plus.AssociatedGraded.compInclusionIso

namespace Minus.AssociatedGraded.compInclusionIso

/-- The forward bounded-above associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.AssociatedGraded.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-above associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.AssociatedGraded.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded-above associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Minus.ι.map ((Minus.AssociatedGraded.homotopy C).map f) ≫
        (Minus.AssociatedGraded.compInclusionIso C).hom.app Y =
      (Minus.AssociatedGraded.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-above associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Minus.AssociatedGraded.compInclusionIso C).inv.app Y =
      (Minus.AssociatedGraded.compInclusionIso C).inv.app X ≫
        DerivedCategory.Minus.ι.map ((Minus.AssociatedGraded.homotopy C).map f) := sorry

end Minus.AssociatedGraded.compInclusionIso

namespace Bounded.AssociatedGraded.compInclusionIso

/-- The forward bounded associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.AssociatedGraded.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded associated-graded comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.AssociatedGraded.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map ((Bounded.AssociatedGraded.homotopy C).map f) ≫
        (Bounded.AssociatedGraded.compInclusionIso C).hom.app Y =
      (Bounded.AssociatedGraded.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered associated-graded comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) ≫
        (Bounded.AssociatedGraded.compInclusionIso C).inv.app Y =
      (Bounded.AssociatedGraded.compInclusionIso C).inv.app X ≫
        DerivedCategory.Bounded.ι.map ((Bounded.AssociatedGraded.homotopy C).map f) := sorry

end Bounded.AssociatedGraded.compInclusionIso

end CategoryTheory.FilteredObject.FiniteDerived
