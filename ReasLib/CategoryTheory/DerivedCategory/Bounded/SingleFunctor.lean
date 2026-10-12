/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Single Objects in Bounded Derived Categories

@stack 015A
@stack 0FCP

This module supplies the shift-compatible single-object functors into the
bounded-above and bounded derived categories.  The construction mirrors
Mathlib's `DerivedCategory.Plus.singleFunctors`, so all three boundedness
variants expose the same family-level API.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory.Minus

/-- A derived object concentrated in one degree is bounded above. -/
theorem single_obj_mem (n : ℤ) (X : C) :
    (t.minus : ObjectProperty (DerivedCategory C))
      ((DerivedCategory.singleFunctor C n).obj X) := sorry

/-- The shift-compatible family of single-object functors into `D⁻(C)`. -/
@[stacks 015A]
noncomputable def singleFunctors : SingleFunctors C (DerivedCategory.Minus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) DerivedCategory.Minus.ι
    (fun n ↦ (t.minus : ObjectProperty (DerivedCategory C)).lift
      (DerivedCategory.singleFunctor C n) (single_obj_mem C n))
    (fun _ ↦ Iso.refl _)

/-- The functor sending an object of `C` to the object of `D⁻(C)` concentrated
in degree `n`. -/
@[stacks 015A]
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ DerivedCategory.Minus C :=
  (singleFunctors C).functor n

/-- Forgetting bounded-above support recovers the ambient derived single-object
functor. -/
@[stacks 015A]
noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.singleFunctor C n :=
  Iso.refl _

/-- Every bounded-above single-object functor is additive. -/
instance singleFunctor.additive (n : ℤ) : (singleFunctor C n).Additive := sorry

end DerivedCategory.Minus

namespace DerivedCategory.Bounded

/-- A derived object concentrated in one degree is bounded. -/
theorem single_obj_mem (n : ℤ) (X : C) :
    (t.bounded : ObjectProperty (DerivedCategory C))
      ((DerivedCategory.singleFunctor C n).obj X) := sorry

/-- The shift-compatible family of single-object functors into `Dᵇ(C)`. -/
@[stacks 0FCP]
noncomputable def singleFunctors : SingleFunctors C (DerivedCategory.Bounded C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) DerivedCategory.Bounded.ι
    (fun n ↦ (t.bounded : ObjectProperty (DerivedCategory C)).lift
      (DerivedCategory.singleFunctor C n) (single_obj_mem C n))
    (fun _ ↦ Iso.refl _)

/-- The functor sending an object of `C` to the object of `Dᵇ(C)` concentrated
in degree `n`. -/
@[stacks 0FCP]
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ DerivedCategory.Bounded C :=
  (singleFunctors C).functor n

/-- Forgetting bounded support recovers the ambient derived single-object
functor. -/
@[stacks 0FCP]
noncomputable def singleFunctorιIso (n : ℤ) :
    singleFunctor C n ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.singleFunctor C n :=
  Iso.refl _

/-- Every bounded single-object functor is additive. -/
instance singleFunctor.additive (n : ℤ) : (singleFunctor C n).Additive := sorry

end DerivedCategory.Bounded



end CategoryTheory
