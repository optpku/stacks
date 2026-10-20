/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive.Computation

/-!
# Components of bounded graded-piece comparisons

The bounded graded-piece comparison has two layers: the bounded-to-unbounded
comparison is identity, while evaluation after associated graded is compared
with the composite functor by `Functor.Homotopy.Comp.iso`.  The statements in
this leaf expose exactly that remaining nontrivial component.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C]

namespace Plus.GradedPiece.compInclusionIso

/-- The forward bounded-below graded-piece comparison is the generic composite
comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_app (p : ℤ)
    (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.GradedPiece.compInclusionIso C p).hom.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).hom.app
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- The inverse bounded-below graded-piece comparison is the inverse generic
composite comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_app (p : ℤ)
    (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    (Plus.GradedPiece.compInclusionIso C p).inv.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).inv.app
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- Forward naturality of the bounded-below graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_naturality (p : ℤ)
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map ((Plus.GradedPiece.homotopy C p).map f) ≫
        (Plus.GradedPiece.compInclusionIso C p).hom.app Y =
      (Plus.GradedPiece.compInclusionIso C p).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-below graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_naturality (p : ℤ)
    {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Plus.GradedPiece.compInclusionIso C p).inv.app Y =
      (Plus.GradedPiece.compInclusionIso C p).inv.app X ≫
        DerivedCategory.Plus.ι.map ((Plus.GradedPiece.homotopy C p).map f) := sorry

end Plus.GradedPiece.compInclusionIso

namespace Minus.GradedPiece.compInclusionIso

/-- The forward bounded-above graded-piece comparison is the generic composite
comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_app (p : ℤ)
    (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.GradedPiece.compInclusionIso C p).hom.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).hom.app
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- The inverse bounded-above graded-piece comparison is the inverse generic
composite comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_app (p : ℤ)
    (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    (Minus.GradedPiece.compInclusionIso C p).inv.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).inv.app
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- Forward naturality of the bounded-above graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_naturality (p : ℤ)
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Minus.ι.map ((Minus.GradedPiece.homotopy C p).map f) ≫
        (Minus.GradedPiece.compInclusionIso C p).hom.app Y =
      (Minus.GradedPiece.compInclusionIso C p).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded-above graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_naturality (p : ℤ)
    {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)).map f) ≫
        (Minus.GradedPiece.compInclusionIso C p).inv.app Y =
      (Minus.GradedPiece.compInclusionIso C p).inv.app X ≫
        DerivedCategory.Minus.ι.map ((Minus.GradedPiece.homotopy C p).map f) := sorry

end Minus.GradedPiece.compInclusionIso

namespace Bounded.GradedPiece.compInclusionIso

/-- The forward bounded graded-piece comparison is the generic composite
comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_app (p : ℤ)
    (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.GradedPiece.compInclusionIso C p).hom.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).hom.app
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- The inverse bounded graded-piece comparison is the inverse generic
composite comparison at the included homotopy object. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_app (p : ℤ)
    (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    (Bounded.GradedPiece.compInclusionIso C p).inv.app X =
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C)
        (GradedObject.eval p)).inv.app
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).obj X) := sorry

/-- Forward naturality of the bounded graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem hom_naturality (p : ℤ)
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map ((Bounded.GradedPiece.homotopy C p).map f) ≫
        (Bounded.GradedPiece.compInclusionIso C p).hom.app Y =
      (Bounded.GradedPiece.compInclusionIso C p).hom.app X ≫
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) := sorry

/-- Inverse naturality of the bounded graded-piece comparison. -/
@[reassoc (attr := simp), stacks 05S6 "bounded finite filtered graded-piece comparison"]
theorem inv_naturality (p : ℤ)
    {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p).map
          ((HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)).map f) ≫
        (Bounded.GradedPiece.compInclusionIso C p).inv.app Y =
      (Bounded.GradedPiece.compInclusionIso C p).inv.app X ≫
        DerivedCategory.Bounded.ι.map ((Bounded.GradedPiece.homotopy C p).map f) := sorry

end Bounded.GradedPiece.compInclusionIso

end CategoryTheory.FilteredObject.FiniteDerived
