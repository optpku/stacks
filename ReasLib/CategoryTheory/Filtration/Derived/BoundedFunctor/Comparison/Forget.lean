/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Comparison

/-!
# Components of bounded forgetful comparisons

Forgetting a finite filtration before or after passing from a bounded homotopy
category to the ambient derived category gives canonically identical functors.
This leaf exposes the identity components and their naturality.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C]

namespace Plus.Forget.compInclusionIso

/-- The forward bounded-below forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Forget.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-below forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.Forget.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded-below forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map ((Plus.Forget.homotopy C).map f) ≫
        (Plus.Forget.compInclusionIso C).hom.app Y =
      (Plus.Forget.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-below forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Plus.Forget.compInclusionIso C).inv.app Y =
      (Plus.Forget.compInclusionIso C).inv.app X ≫
        DerivedCategory.Plus.ι.map ((Plus.Forget.homotopy C).map f) := sorry

end Plus.Forget.compInclusionIso

namespace Minus.Forget.compInclusionIso

/-- The forward bounded-above forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Forget.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-above forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.Forget.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded-above forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Minus.ι.map ((Minus.Forget.homotopy C).map f) ≫
        (Minus.Forget.compInclusionIso C).hom.app Y =
      (Minus.Forget.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-above forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Minus.Forget.compInclusionIso C).inv.app Y =
      (Minus.Forget.compInclusionIso C).inv.app X ≫
        DerivedCategory.Minus.ι.map ((Minus.Forget.homotopy C).map f) := sorry

end Minus.Forget.compInclusionIso

namespace Bounded.Forget.compInclusionIso

/-- The forward bounded forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Forget.compInclusionIso C).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded forgetful comparison is objectwise identity. -/
@[simp, stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_app (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.Forget.compInclusionIso C).inv.app X = 𝟙 _ := sorry

/-- Forward naturality of the bounded forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem hom_naturality
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map ((Bounded.Forget.homotopy C).map f) ≫
        (Bounded.Forget.compInclusionIso C).hom.app Y =
      (Bounded.Forget.compInclusionIso C).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded forgetful comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered forgetful comparison"]
theorem inv_naturality
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) ≫
        (Bounded.Forget.compInclusionIso C).inv.app Y =
      (Bounded.Forget.compInclusionIso C).inv.app X ≫
        DerivedCategory.Bounded.ι.map ((Bounded.Forget.homotopy C).map f) := sorry

end Bounded.Forget.compInclusionIso

end CategoryTheory.FilteredObject.FiniteDerived
