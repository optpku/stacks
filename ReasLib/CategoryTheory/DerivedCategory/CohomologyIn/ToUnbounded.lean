/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded Cohomology-In Subcategories Inside the Unbounded One

The bounded-below, bounded-above, and bounded cohomology-in subcategories map canonically to the
unbounded cohomology-in subcategory.  This leaf exposes the three functors and their inclusion-level
computation API without requiring downstream users to reconstruct full-subcategory restrictions.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.Plus.CohomologyIn

/-- Regard a bounded-below cohomology-in object as an unbounded cohomology-in object. -/
@[stacks 06UQ "bounded-below cohomology-in inclusion into the unbounded subcategory"]
abbrev toUnbounded (P : ObjectProperty A) :
    DerivedCategory.Plus.CohomologyIn P ⥤ DerivedCategory.CohomologyIn P :=
  ObjectProperty.FullSubcategory.restrict DerivedCategory.Plus.ι (fun _ h => h)

namespace toUnbounded

/-- The underlying derived object of the bounded-below inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded-below cohomology-in inclusion object"]
theorem obj_obj (P : ObjectProperty A) (X : DerivedCategory.Plus.CohomologyIn P) :
    ((toUnbounded P).obj X).obj = DerivedCategory.Plus.ι.obj X.obj := sorry

/-- The underlying morphism of the bounded-below inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded-below cohomology-in inclusion morphism"]
theorem map_hom (P : ObjectProperty A) {X Y : DerivedCategory.Plus.CohomologyIn P}
    (f : X ⟶ Y) :
    ((toUnbounded P).map f).hom = DerivedCategory.Plus.ι.map f.hom := sorry

/-- Forgetting the bounded-below cohomology-in inclusion recovers its ambient inclusion. -/
@[stacks 06UQ "bounded-below cohomology-in ambient comparison"]
def compιIso (P : ObjectProperty A) :
    toUnbounded P ⋙ (DerivedCategory.cohomologyIn P).ι ≅
      DerivedCategory.Plus.CohomologyIn.ambient P :=
  ObjectProperty.FullSubcategory.restrict.compιIso DerivedCategory.Plus.ι (fun _ h => h)

/-- The forward ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded-below cohomology-in ambient comparison component"]
theorem compιIso_hom_app (P : ObjectProperty A) (X : DerivedCategory.Plus.CohomologyIn P) :
    (compιIso P).hom.app X = 𝟙 (DerivedCategory.Plus.ι.obj X.obj) := sorry

/-- The inverse ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded-below cohomology-in inverse ambient comparison component"]
theorem compιIso_inv_app (P : ObjectProperty A) (X : DerivedCategory.Plus.CohomologyIn P) :
    (compιIso P).inv.app X = 𝟙 (DerivedCategory.Plus.ι.obj X.obj) := sorry

end toUnbounded

end DerivedCategory.Plus.CohomologyIn

namespace DerivedCategory.Minus.CohomologyIn

/-- Regard a bounded-above cohomology-in object as an unbounded cohomology-in object. -/
@[stacks 06UQ "bounded-above cohomology-in inclusion into the unbounded subcategory"]
abbrev toUnbounded (P : ObjectProperty A) :
    DerivedCategory.Minus.CohomologyIn P ⥤ DerivedCategory.CohomologyIn P :=
  ObjectProperty.FullSubcategory.restrict DerivedCategory.Minus.ι (fun _ h => h)

namespace toUnbounded

/-- The underlying derived object of the bounded-above inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded-above cohomology-in inclusion object"]
theorem obj_obj (P : ObjectProperty A) (X : DerivedCategory.Minus.CohomologyIn P) :
    ((toUnbounded P).obj X).obj = DerivedCategory.Minus.ι.obj X.obj := sorry

/-- The underlying morphism of the bounded-above inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded-above cohomology-in inclusion morphism"]
theorem map_hom (P : ObjectProperty A) {X Y : DerivedCategory.Minus.CohomologyIn P}
    (f : X ⟶ Y) :
    ((toUnbounded P).map f).hom = DerivedCategory.Minus.ι.map f.hom := sorry

/-- Forgetting the bounded-above cohomology-in inclusion recovers its ambient inclusion. -/
@[stacks 06UQ "bounded-above cohomology-in ambient comparison"]
def compιIso (P : ObjectProperty A) :
    toUnbounded P ⋙ (DerivedCategory.cohomologyIn P).ι ≅
      DerivedCategory.Minus.CohomologyIn.ambient P :=
  ObjectProperty.FullSubcategory.restrict.compιIso DerivedCategory.Minus.ι (fun _ h => h)

/-- The forward ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded-above cohomology-in ambient comparison component"]
theorem compιIso_hom_app (P : ObjectProperty A) (X : DerivedCategory.Minus.CohomologyIn P) :
    (compιIso P).hom.app X = 𝟙 (DerivedCategory.Minus.ι.obj X.obj) := sorry

/-- The inverse ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded-above cohomology-in inverse ambient comparison component"]
theorem compιIso_inv_app (P : ObjectProperty A) (X : DerivedCategory.Minus.CohomologyIn P) :
    (compιIso P).inv.app X = 𝟙 (DerivedCategory.Minus.ι.obj X.obj) := sorry

end toUnbounded

end DerivedCategory.Minus.CohomologyIn

namespace DerivedCategory.Bounded.CohomologyIn

/-- Regard a bounded cohomology-in object as an unbounded cohomology-in object. -/
@[stacks 06UQ "bounded cohomology-in inclusion into the unbounded subcategory"]
abbrev toUnbounded (P : ObjectProperty A) :
    DerivedCategory.Bounded.CohomologyIn P ⥤ DerivedCategory.CohomologyIn P :=
  ObjectProperty.FullSubcategory.restrict DerivedCategory.Bounded.ι (fun _ h => h)

namespace toUnbounded

/-- The underlying derived object of the bounded inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded cohomology-in inclusion object"]
theorem obj_obj (P : ObjectProperty A) (X : DerivedCategory.Bounded.CohomologyIn P) :
    ((toUnbounded P).obj X).obj = DerivedCategory.Bounded.ι.obj X.obj := sorry

/-- The underlying morphism of the bounded inclusion is the ambient inclusion. -/
@[simp, stacks 06UQ "bounded cohomology-in inclusion morphism"]
theorem map_hom (P : ObjectProperty A) {X Y : DerivedCategory.Bounded.CohomologyIn P}
    (f : X ⟶ Y) :
    ((toUnbounded P).map f).hom = DerivedCategory.Bounded.ι.map f.hom := sorry

/-- Forgetting the bounded cohomology-in inclusion recovers its ambient inclusion. -/
@[stacks 06UQ "bounded cohomology-in ambient comparison"]
def compιIso (P : ObjectProperty A) :
    toUnbounded P ⋙ (DerivedCategory.cohomologyIn P).ι ≅
      DerivedCategory.Bounded.CohomologyIn.ambient P :=
  ObjectProperty.FullSubcategory.restrict.compιIso DerivedCategory.Bounded.ι (fun _ h => h)

/-- The forward ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded cohomology-in ambient comparison component"]
theorem compιIso_hom_app (P : ObjectProperty A) (X : DerivedCategory.Bounded.CohomologyIn P) :
    (compιIso P).hom.app X = 𝟙 (DerivedCategory.Bounded.ι.obj X.obj) := sorry

/-- The inverse ambient comparison is componentwise the identity. -/
@[simp, stacks 06UQ "bounded cohomology-in inverse ambient comparison component"]
theorem compιIso_inv_app (P : ObjectProperty A) (X : DerivedCategory.Bounded.CohomologyIn P) :
    (compιIso P).inv.app X = 𝟙 (DerivedCategory.Bounded.ι.obj X.obj) := sorry

end toUnbounded

end DerivedCategory.Bounded.CohomologyIn

end CategoryTheory
