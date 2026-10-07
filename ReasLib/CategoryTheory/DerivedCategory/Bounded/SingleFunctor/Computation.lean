module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Localization

@[expose] public section

/-!
# Computation for Bounded Derived Single Objects

This module exposes component and naturality formulas for the localization
models of single objects.  The data owners remain in `Localization`.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

namespace DerivedCategory.singleFunctor.compQhIso

/-- Naturality of the forward homotopy-to-derived single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "derived single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (HomotopyCategory.singleFunctor C n ⋙ DerivedCategory.Qh).map f ≫
        (DerivedCategory.singleFunctor.compQhIso C n).hom.app Y =
      (DerivedCategory.singleFunctor.compQhIso C n).hom.app X ≫
        (DerivedCategory.singleFunctor C n).map f := sorry

/-- Naturality of the inverse homotopy-to-derived single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "derived single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C n).map f ≫
        (DerivedCategory.singleFunctor.compQhIso C n).inv.app Y =
      (DerivedCategory.singleFunctor.compQhIso C n).inv.app X ≫
        (HomotopyCategory.singleFunctor C n ⋙ DerivedCategory.Qh).map f := sorry

end DerivedCategory.singleFunctor.compQhIso

namespace DerivedCategory.Plus.singleFunctor.fromHomotopy

namespace compInclusionIso

/-- Naturality of the forward bounded-below localization comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n ⋙ DerivedCategory.Plus.ι).map f ≫
        (compInclusionIso C n).hom.app Y =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded-below localization comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C n).map f ≫ (compInclusionIso C n).inv.app Y =
      (compInclusionIso C n).inv.app X ≫
        (fromHomotopy C n ⋙ DerivedCategory.Plus.ι).map f := sorry

end compInclusionIso

namespace iso

/-- After inclusion in the ambient derived category, the forward component of the canonical
bounded-below single-object comparison is the explicit localization comparison. -/
@[simp, stacks 015A "bounded-below single-object localization computation"]
theorem hom_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((iso C n).hom.app X) =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.Plus.singleFunctorιIso C n).inv.app X := sorry

/-- After inclusion in the ambient derived category, the inverse component of the canonical
bounded-below single-object comparison is the inverse explicit localization comparison. -/
@[simp, stacks 015A "bounded-below single-object localization computation"]
theorem inv_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((iso C n).inv.app X) =
      (DerivedCategory.Plus.singleFunctorιIso C n).hom.app X ≫
        (compInclusionIso C n).inv.app X := sorry

/-- Naturality of the forward bounded-below single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n).map f ≫ (iso C n).hom.app Y =
      (iso C n).hom.app X ≫ (DerivedCategory.Plus.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded-below single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-below single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.Plus.singleFunctor C n).map f ≫ (iso C n).inv.app Y =
      (iso C n).inv.app X ≫ (fromHomotopy C n).map f := sorry

end iso

end DerivedCategory.Plus.singleFunctor.fromHomotopy

namespace DerivedCategory.Minus.singleFunctor.fromHomotopy

namespace compInclusionIso

/-- Naturality of the forward bounded-above localization comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n ⋙ DerivedCategory.Minus.ι).map f ≫
        (compInclusionIso C n).hom.app Y =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded-above localization comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C n).map f ≫ (compInclusionIso C n).inv.app Y =
      (compInclusionIso C n).inv.app X ≫
        (fromHomotopy C n ⋙ DerivedCategory.Minus.ι).map f := sorry

end compInclusionIso

namespace iso

/-- After inclusion in the ambient derived category, the forward component of the canonical
bounded-above single-object comparison is the explicit localization comparison. -/
@[simp, stacks 015A "bounded-above single-object localization computation"]
theorem hom_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Minus.ι.map ((iso C n).hom.app X) =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.Minus.singleFunctorιIso C n).inv.app X := sorry

/-- After inclusion in the ambient derived category, the inverse component of the canonical
bounded-above single-object comparison is the inverse explicit localization comparison. -/
@[simp, stacks 015A "bounded-above single-object localization computation"]
theorem inv_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Minus.ι.map ((iso C n).inv.app X) =
      (DerivedCategory.Minus.singleFunctorιIso C n).hom.app X ≫
        (compInclusionIso C n).inv.app X := sorry

/-- Naturality of the forward bounded-above single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n).map f ≫ (iso C n).hom.app Y =
      (iso C n).hom.app X ≫ (DerivedCategory.Minus.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded-above single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.Minus.singleFunctor C n).map f ≫ (iso C n).inv.app Y =
      (iso C n).inv.app X ≫ (fromHomotopy C n).map f := sorry

end iso

end DerivedCategory.Minus.singleFunctor.fromHomotopy

namespace DerivedCategory.Bounded.singleFunctor.fromHomotopy

namespace compInclusionIso

/-- Naturality of the forward bounded single-object localization comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n ⋙ DerivedCategory.Bounded.ι).map f ≫
        (compInclusionIso C n).hom.app Y =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded single-object localization comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C n).map f ≫ (compInclusionIso C n).inv.app Y =
      (compInclusionIso C n).inv.app X ≫
        (fromHomotopy C n ⋙ DerivedCategory.Bounded.ι).map f := sorry

end compInclusionIso

namespace iso

/-- After inclusion in the ambient derived category, the forward component of the canonical
bounded single-object comparison is the explicit localization comparison. -/
@[simp, stacks 0FCP "bounded single-object localization computation"]
theorem hom_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Bounded.ι.map ((iso C n).hom.app X) =
      (compInclusionIso C n).hom.app X ≫
        (DerivedCategory.Bounded.singleFunctorιIso C n).inv.app X := sorry

/-- After inclusion in the ambient derived category, the inverse component of the canonical
bounded single-object comparison is the inverse explicit localization comparison. -/
@[simp, stacks 0FCP "bounded single-object localization computation"]
theorem inv_app_inclusion (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) (X : C) :
    DerivedCategory.Bounded.ι.map ((iso C n).inv.app X) =
      (DerivedCategory.Bounded.singleFunctorιIso C n).hom.app X ≫
        (compInclusionIso C n).inv.app X := sorry

/-- Naturality of the forward bounded single-object comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single-object localization comparison"]
theorem hom_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (fromHomotopy C n).map f ≫ (iso C n).hom.app Y =
      (iso C n).hom.app X ≫ (DerivedCategory.Bounded.singleFunctor C n).map f := sorry

/-- Naturality of the inverse bounded single-object comparison. -/
@[reassoc (attr := simp), stacks 0FCP "bounded single-object localization comparison"]
theorem inv_naturality (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.Bounded.singleFunctor C n).map f ≫ (iso C n).inv.app Y =
      (iso C n).inv.app X ≫ (fromHomotopy C n).map f := sorry

end iso

end DerivedCategory.Bounded.singleFunctor.fromHomotopy

end CategoryTheory
