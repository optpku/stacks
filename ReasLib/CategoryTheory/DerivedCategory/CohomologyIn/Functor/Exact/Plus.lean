module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact functors on bounded-below cohomology-in subcategories

This leaf owns the generic restriction of an exact derived functor to the
bounded-below objects whose cohomology satisfies a chosen object property.
The coefficient relation is an explicit argument, so ringed-site instances
can specialize it without rebuilding the derived-category infrastructure.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived.Plus.CohomologyIn

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B]

/-- An exact functor carries the bounded-below cohomology-in property along a
coefficient-level inclusion. -/
@[stacks 015F "exact functor maps bounded-below cohomology-in objects"]
theorem mapsTo (F : A ⥤ₑ B) (P : ObjectProperty A) (Q : ObjectProperty B)
    (hPQ : P ≤ Q.inverseImage F.obj) :
    DerivedCategory.Plus.cohomologyIn P ≤
      (DerivedCategory.Plus.cohomologyIn Q).inverseImage
        (ExactFunctor.Derived.Plus.functor F) := sorry

/-- The bounded-below derived restriction of an exact functor to
cohomology-in full subcategories. -/
@[stacks 015F "bounded-below exact cohomology-in restriction"]
noncomputable abbrev functor (F : A ⥤ₑ B) (P : ObjectProperty A)
    (Q : ObjectProperty B) (hPQ : P ≤ Q.inverseImage F.obj) :
    DerivedCategory.Plus.CohomologyIn P ⥤
      DerivedCategory.Plus.CohomologyIn Q :=
  ObjectProperty.FullSubcategory.restrict
    (ExactFunctor.Derived.Plus.functor F)
    (mapsTo F P Q hPQ)

/-- The inclusion comparison for the bounded-below exact cohomology-in
restriction. -/
@[stacks 015F "bounded-below exact cohomology-in inclusion comparison"]
noncomputable abbrev compιIso (F : A ⥤ₑ B) (P : ObjectProperty A)
    (Q : ObjectProperty B) (hPQ : P ≤ Q.inverseImage F.obj) :
    functor F P Q hPQ ⋙ (DerivedCategory.Plus.cohomologyIn Q).ι ≅
      (DerivedCategory.Plus.cohomologyIn P).ι ⋙
        ExactFunctor.Derived.Plus.functor F :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (ExactFunctor.Derived.Plus.functor F)
    (mapsTo F P Q hPQ)

end CategoryTheory.ExactFunctor.Derived.Plus.CohomologyIn

end
