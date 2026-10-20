/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computation for Bounded Derived Localizations

This leaf records componentwise naturality for the comparison between each
bounded localization followed by its inclusion and the ambient derived
localization.  The bounded-above and bounded comparisons are definitionally
the identity, so their components also have simp lemmas.
-/

open CategoryTheory
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.Plus.Qh.compInclusionIso

/-- Naturality of the forward bounded-below localization comparison. -/
@[reassoc (attr := simp), stacks 0159 "bounded-below localization comparison"]
theorem hom_naturality {X Y : CochainComplex.Plus A} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f) ≫
        (DerivedCategory.Plus.Qh.compInclusionIso A).hom.app Y =
      (DerivedCategory.Plus.Qh.compInclusionIso A).hom.app X ≫
        DerivedCategory.Q.map ((CochainComplex.Plus.ι A).map f) := sorry

/-- Naturality of the inverse bounded-below localization comparison. -/
@[reassoc (attr := simp), stacks 0159 "bounded-below localization comparison"]
theorem inv_naturality {X Y : CochainComplex.Plus A} (f : X ⟶ Y) :
    DerivedCategory.Q.map ((CochainComplex.Plus.ι A).map f) ≫
        (DerivedCategory.Plus.Qh.compInclusionIso A).inv.app Y =
      (DerivedCategory.Plus.Qh.compInclusionIso A).inv.app X ≫
        DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f) := sorry

end DerivedCategory.Plus.Qh.compInclusionIso

namespace DerivedCategory.Minus.Qh.compInclusionIso

/-- The forward bounded-above localization comparison has identity components. -/
@[simp, stacks 05RW "bounded-above localization comparison"]
theorem hom_app (X : HomotopyCategory.Minus A) :
    (DerivedCategory.Minus.Qh.compInclusionIso A).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded-above localization comparison has identity components. -/
@[simp, stacks 05RW "bounded-above localization comparison"]
theorem inv_app (X : HomotopyCategory.Minus A) :
    (DerivedCategory.Minus.Qh.compInclusionIso A).inv.app X = 𝟙 _ := sorry

/-- Naturality of the forward bounded-above localization comparison. -/
@[reassoc (attr := simp), stacks 05RW "bounded-above localization comparison"]
theorem hom_naturality {X Y : HomotopyCategory.Minus A} (f : X ⟶ Y) :
    DerivedCategory.Minus.ι.map ((DerivedCategory.Minus.Qh A).map f) ≫
        (DerivedCategory.Minus.Qh.compInclusionIso A).hom.app Y =
      (DerivedCategory.Minus.Qh.compInclusionIso A).hom.app X ≫
        DerivedCategory.Qh.map ((HomotopyCategory.minus A).ι.map f) := sorry

/-- Naturality of the inverse bounded-above localization comparison. -/
@[reassoc (attr := simp), stacks 05RW "bounded-above localization comparison"]
theorem inv_naturality {X Y : HomotopyCategory.Minus A} (f : X ⟶ Y) :
    DerivedCategory.Qh.map ((HomotopyCategory.minus A).ι.map f) ≫
        (DerivedCategory.Minus.Qh.compInclusionIso A).inv.app Y =
      (DerivedCategory.Minus.Qh.compInclusionIso A).inv.app X ≫
        DerivedCategory.Minus.ι.map ((DerivedCategory.Minus.Qh A).map f) := sorry

end DerivedCategory.Minus.Qh.compInclusionIso

namespace DerivedCategory.Bounded.Qh.compInclusionIso

/-- The forward bounded localization comparison has identity components. -/
@[simp, stacks 05RW "bounded localization comparison"]
theorem hom_app (X : HomotopyCategory.Bounded A) :
    (DerivedCategory.Bounded.Qh.compInclusionIso A).hom.app X = 𝟙 _ := sorry

/-- The inverse bounded localization comparison has identity components. -/
@[simp, stacks 05RW "bounded localization comparison"]
theorem inv_app (X : HomotopyCategory.Bounded A) :
    (DerivedCategory.Bounded.Qh.compInclusionIso A).inv.app X = 𝟙 _ := sorry

/-- Naturality of the forward bounded localization comparison. -/
@[reassoc (attr := simp), stacks 05RW "bounded localization comparison"]
theorem hom_naturality {X Y : HomotopyCategory.Bounded A} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map ((DerivedCategory.Bounded.Qh A).map f) ≫
        (DerivedCategory.Bounded.Qh.compInclusionIso A).hom.app Y =
      (DerivedCategory.Bounded.Qh.compInclusionIso A).hom.app X ≫
        DerivedCategory.Qh.map ((HomotopyCategory.bounded A).ι.map f) := sorry

/-- Naturality of the inverse bounded localization comparison. -/
@[reassoc (attr := simp), stacks 05RW "bounded localization comparison"]
theorem inv_naturality {X Y : HomotopyCategory.Bounded A} (f : X ⟶ Y) :
    DerivedCategory.Qh.map ((HomotopyCategory.bounded A).ι.map f) ≫
        (DerivedCategory.Bounded.Qh.compInclusionIso A).inv.app Y =
      (DerivedCategory.Bounded.Qh.compInclusionIso A).inv.app X ≫
        DerivedCategory.Bounded.ι.map ((DerivedCategory.Bounded.Qh A).map f) := sorry

end DerivedCategory.Bounded.Qh.compInclusionIso

end CategoryTheory
