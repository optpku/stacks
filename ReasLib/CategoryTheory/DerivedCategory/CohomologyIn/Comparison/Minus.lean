/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Above Derived Comparison

This file restricts the weak-Serre derived comparison to bounded-above
objects. Under the epi-lift condition, the comparison is an equivalence.
-/

open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Minus.CohomologyIn.Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A)

section Basic

variable [IsWeakSerreClass P]
variable [HasDerivedCategory.{w} P.FullSubcategory]

namespace Ambient

/-- The derived functor of the weak Serre inclusion preserves bounded-above
objects. -/
theorem obj_mem (X : DerivedCategory.Minus P.FullSubcategory) :
    (t.minus : ObjectProperty (DerivedCategory A))
      ((DerivedCategory.Minus.ι ⋙ P.ι.mapDerivedCategory).obj X) := sorry

/-- The restriction of the derived weak Serre inclusion to bounded-above
derived categories. -/
noncomputable abbrev functor :
    DerivedCategory.Minus P.FullSubcategory ⥤ DerivedCategory.Minus A :=
  (t.minus : ObjectProperty (DerivedCategory A)).lift
    (DerivedCategory.Minus.ι ⋙ P.ι.mapDerivedCategory) (obj_mem P)

/-- Forgetting the bounded-above restriction recovers the unbounded derived
inclusion on bounded-above objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ P.ι.mapDerivedCategory :=
  (t.minus : ObjectProperty (DerivedCategory A)).liftCompιIso
    (DerivedCategory.Minus.ι ⋙ P.ι.mapDerivedCategory) (obj_mem P)

namespace functor

/-- The underlying object of the bounded-above ambient restriction is the
ordinary derived image under the inclusion. -/
@[simp, stacks 0FCL "bounded-above ambient comparison object computation"]
theorem obj_obj (X : DerivedCategory.Minus P.FullSubcategory) :
    ((functor P).obj X).obj = P.ι.mapDerivedCategory.obj X.obj := sorry

/-- The underlying morphism of the bounded-above ambient restriction is the
ordinary derived map under the inclusion. -/
@[simp, stacks 0FCL "bounded-above ambient comparison map computation"]
theorem map_hom {X Y : DerivedCategory.Minus P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = P.ι.mapDerivedCategory.map f.hom := sorry

end functor

end Ambient

/-- The bounded-above derived functor of the weak Serre inclusion has
cohomology in the ambient object property. -/
theorem obj_mem (X : DerivedCategory.Minus P.FullSubcategory) :
    DerivedCategory.Minus.cohomologyIn P ((Ambient.functor P).obj X) := sorry

/-- The canonical bounded-above comparison from the derived category of the
weak Serre full subcategory to the ambient cohomology-in subcategory. -/
@[stacks 0FCL]
noncomputable abbrev functor :
    DerivedCategory.Minus P.FullSubcategory ⥤
      DerivedCategory.Minus.CohomologyIn P :=
  (DerivedCategory.Minus.cohomologyIn P).lift
    (Ambient.functor P) (obj_mem P)

/-- Forgetting the bounded-above comparison recovers the bounded-above
derived functor of the inclusion. -/
noncomputable def compιIso :
    functor P ⋙ (DerivedCategory.Minus.cohomologyIn P).ι ≅
      Ambient.functor P :=
  (DerivedCategory.Minus.cohomologyIn P).liftCompιIso
    (Ambient.functor P) (obj_mem P)

namespace functor

/-- Forgetting the cohomology condition on a bounded-above comparison object
recovers the ambient bounded-above restriction. -/
@[simp, stacks 0FCL "bounded-above comparison object computation"]
theorem obj_obj (X : DerivedCategory.Minus P.FullSubcategory) :
    ((functor P).obj X).obj = (Ambient.functor P).obj X := sorry

/-- Forgetting the cohomology condition on a bounded-above comparison map
recovers the ambient bounded-above restriction. -/
@[simp, stacks 0FCL "bounded-above comparison map computation"]
theorem map_hom {X Y : DerivedCategory.Minus P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom = (Ambient.functor P).map f := sorry

end functor

end Basic

section Equivalence

variable [P.IsSerreClass]
variable [HasDerivedCategory.{w} P.FullSubcategory]

/-- The bounded-above derived comparison is an equivalence for a Serre class
satisfying the epi-lift condition. -/
@[stacks 0FCL]
instance isEquivalence [P.HasEpiLift] : Functor.IsEquivalence (functor P) := sorry

variable [P.HasEpiLift]

#synth (functor P).EssSurj
#synth (functor P).Full
#synth (functor P).Faithful

end Equivalence

end CategoryTheory.DerivedCategory.Minus.CohomologyIn.Comparison
