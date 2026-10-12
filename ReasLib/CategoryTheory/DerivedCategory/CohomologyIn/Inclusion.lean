/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inclusions Between Cohomology-In Subcategories

An inclusion of coefficient object properties induces fully faithful functors between the
corresponding cohomology-in subcategories.  This leaf exposes those functors uniformly for the
unbounded, bounded-below, bounded-above, and bounded derived categories.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.CohomologyIn

/-- An inclusion of coefficient properties induces an inclusion of cohomology-in
subcategories. -/
@[stacks 06UQ "inclusion of derived cohomology-in subcategories"]
noncomputable def inclusion {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.CohomologyIn P ⥤ DerivedCategory.CohomologyIn Q :=
  ObjectProperty.ιOfLE (monotone h)

namespace inclusion

/-- The underlying object of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "derived cohomology-in inclusion object"]
theorem obj_obj {P Q : ObjectProperty A} (h : P ≤ Q)
    (X : DerivedCategory.CohomologyIn P) :
    ((inclusion h).obj X).obj = X.obj := sorry

/-- The underlying morphism of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "derived cohomology-in inclusion morphism"]
theorem map_hom {P Q : ObjectProperty A} (h : P ≤ Q)
    {X Y : DerivedCategory.CohomologyIn P} (f : X ⟶ Y) :
    ((inclusion h).map f).hom = f.hom := sorry

/-- Composing a cohomology-in inclusion with the ambient inclusion recovers the original
ambient inclusion. -/
@[stacks 06UQ "derived cohomology-in inclusion comparison"]
noncomputable def compιIso {P Q : ObjectProperty A} (h : P ≤ Q) :
    inclusion h ⋙ (DerivedCategory.cohomologyIn Q).ι ≅
      (DerivedCategory.cohomologyIn P).ι :=
  ObjectProperty.ιOfLECompιIso (monotone h)

/-- A cohomology-in inclusion is full. -/
@[stacks 06UQ "full derived cohomology-in inclusion"]
instance full {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Full := sorry

/-- A cohomology-in inclusion is faithful. -/
@[stacks 06UQ "faithful derived cohomology-in inclusion"]
instance faithful {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Faithful := sorry

end inclusion

end DerivedCategory.CohomologyIn

namespace DerivedCategory.Plus.CohomologyIn

/-- An inclusion of coefficient properties induces an inclusion of bounded-below
cohomology-in subcategories. -/
@[stacks 06UQ "inclusion of bounded-below cohomology-in subcategories"]
noncomputable def inclusion {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Plus.CohomologyIn P ⥤ DerivedCategory.Plus.CohomologyIn Q :=
  ObjectProperty.ιOfLE (monotone h)

namespace inclusion

/-- The underlying bounded-below object of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded-below cohomology-in inclusion object"]
theorem obj_obj {P Q : ObjectProperty A} (h : P ≤ Q)
    (X : DerivedCategory.Plus.CohomologyIn P) :
    ((inclusion h).obj X).obj = X.obj := sorry

/-- The underlying bounded-below morphism of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded-below cohomology-in inclusion morphism"]
theorem map_hom {P Q : ObjectProperty A} (h : P ≤ Q)
    {X Y : DerivedCategory.Plus.CohomologyIn P} (f : X ⟶ Y) :
    ((inclusion h).map f).hom = f.hom := sorry

/-- The bounded-below cohomology-in inclusion commutes with the canonical full-subcategory
inclusions. -/
@[stacks 06UQ "bounded-below cohomology-in inclusion comparison"]
noncomputable def compιIso {P Q : ObjectProperty A} (h : P ≤ Q) :
    inclusion h ⋙ (DerivedCategory.Plus.cohomologyIn Q).ι ≅
      (DerivedCategory.Plus.cohomologyIn P).ι :=
  ObjectProperty.ιOfLECompιIso (monotone h)

/-- A bounded-below cohomology-in inclusion is full. -/
@[stacks 06UQ "full bounded-below cohomology-in inclusion"]
instance full {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Full := sorry

/-- A bounded-below cohomology-in inclusion is faithful. -/
@[stacks 06UQ "faithful bounded-below cohomology-in inclusion"]
instance faithful {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Faithful := sorry

end inclusion

end DerivedCategory.Plus.CohomologyIn

namespace DerivedCategory.Minus.CohomologyIn

/-- An inclusion of coefficient properties induces an inclusion of bounded-above
cohomology-in subcategories. -/
@[stacks 06UQ "inclusion of bounded-above cohomology-in subcategories"]
noncomputable def inclusion {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Minus.CohomologyIn P ⥤ DerivedCategory.Minus.CohomologyIn Q :=
  ObjectProperty.ιOfLE (monotone h)

namespace inclusion

/-- The underlying bounded-above object of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded-above cohomology-in inclusion object"]
theorem obj_obj {P Q : ObjectProperty A} (h : P ≤ Q)
    (X : DerivedCategory.Minus.CohomologyIn P) :
    ((inclusion h).obj X).obj = X.obj := sorry

/-- The underlying bounded-above morphism of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded-above cohomology-in inclusion morphism"]
theorem map_hom {P Q : ObjectProperty A} (h : P ≤ Q)
    {X Y : DerivedCategory.Minus.CohomologyIn P} (f : X ⟶ Y) :
    ((inclusion h).map f).hom = f.hom := sorry

/-- The bounded-above cohomology-in inclusion commutes with the canonical full-subcategory
inclusions. -/
@[stacks 06UQ "bounded-above cohomology-in inclusion comparison"]
noncomputable def compιIso {P Q : ObjectProperty A} (h : P ≤ Q) :
    inclusion h ⋙ (DerivedCategory.Minus.cohomologyIn Q).ι ≅
      (DerivedCategory.Minus.cohomologyIn P).ι :=
  ObjectProperty.ιOfLECompιIso (monotone h)

/-- A bounded-above cohomology-in inclusion is full. -/
@[stacks 06UQ "full bounded-above cohomology-in inclusion"]
instance full {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Full := sorry

/-- A bounded-above cohomology-in inclusion is faithful. -/
@[stacks 06UQ "faithful bounded-above cohomology-in inclusion"]
instance faithful {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Faithful := sorry

end inclusion

end DerivedCategory.Minus.CohomologyIn

namespace DerivedCategory.Bounded.CohomologyIn

/-- An inclusion of coefficient properties induces an inclusion of bounded cohomology-in
subcategories. -/
@[stacks 06UQ "inclusion of bounded cohomology-in subcategories"]
noncomputable def inclusion {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Bounded.CohomologyIn P ⥤ DerivedCategory.Bounded.CohomologyIn Q :=
  ObjectProperty.ιOfLE (monotone h)

namespace inclusion

/-- The underlying bounded object of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded cohomology-in inclusion object"]
theorem obj_obj {P Q : ObjectProperty A} (h : P ≤ Q)
    (X : DerivedCategory.Bounded.CohomologyIn P) :
    ((inclusion h).obj X).obj = X.obj := sorry

/-- The underlying bounded morphism of a cohomology-in inclusion is unchanged. -/
@[simp, stacks 06UQ "bounded cohomology-in inclusion morphism"]
theorem map_hom {P Q : ObjectProperty A} (h : P ≤ Q)
    {X Y : DerivedCategory.Bounded.CohomologyIn P} (f : X ⟶ Y) :
    ((inclusion h).map f).hom = f.hom := sorry

/-- The bounded cohomology-in inclusion commutes with the canonical full-subcategory
inclusions. -/
@[stacks 06UQ "bounded cohomology-in inclusion comparison"]
noncomputable def compιIso {P Q : ObjectProperty A} (h : P ≤ Q) :
    inclusion h ⋙ (DerivedCategory.Bounded.cohomologyIn Q).ι ≅
      (DerivedCategory.Bounded.cohomologyIn P).ι :=
  ObjectProperty.ιOfLECompιIso (monotone h)

/-- A bounded cohomology-in inclusion is full. -/
@[stacks 06UQ "full bounded cohomology-in inclusion"]
instance full {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Full := sorry

/-- A bounded cohomology-in inclusion is faithful. -/
@[stacks 06UQ "faithful bounded cohomology-in inclusion"]
instance faithful {P Q : ObjectProperty A} (h : P ≤ Q) :
    (inclusion h).Faithful := sorry

end inclusion

end DerivedCategory.Bounded.CohomologyIn

end CategoryTheory
