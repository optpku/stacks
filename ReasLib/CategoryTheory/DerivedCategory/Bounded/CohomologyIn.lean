/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Homology
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Homology.Bounded
public import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Derived Objects with Cohomology in an Object Property

This file provides the degree-zero embedding and the homological structure on the lifted
cohomology functor for `DerivedCategory.Bounded.CohomologyIn P`.  The functor and its computation
API are owned by `CohomologyIn.Homology.Bounded`; this bridge adds the bounded-support structure
needed by the `K₀` layer.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A)

namespace Single

/-- A degree-zero object from `P` belongs to the bounded derived subcategory
whose cohomology lies in `P`. -/
@[stacks 0FCS "degree-zero objects have cohomology in the coefficient property"]
theorem obj_mem [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (X : P.FullSubcategory) :
    DerivedCategory.Bounded.cohomologyIn P
      ((P.ι ⋙ DerivedCategory.Bounded.singleFunctor A 0).obj X) := sorry

/-- The degree-zero embedding of `P` into the bounded derived subcategory
with cohomology in `P`. -/
@[stacks 0FCS]
abbrev functor [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.FullSubcategory ⥤ DerivedCategory.Bounded.CohomologyIn P :=
  (DerivedCategory.Bounded.cohomologyIn P).lift
    (P.ι ⋙ DerivedCategory.Bounded.singleFunctor A 0) (obj_mem P)

/-- Forgetting the lifted degree-zero embedding recovers the ordinary
degree-zero embedding into the bounded derived category. -/
@[stacks 0FCS "underlying degree-zero embedding comparison"]
noncomputable def compιIso [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    functor P ⋙ (DerivedCategory.Bounded.cohomologyIn P).ι ≅
      P.ι ⋙ DerivedCategory.Bounded.singleFunctor A 0 :=
  (DerivedCategory.Bounded.cohomologyIn P).liftCompιIso
    (P.ι ⋙ DerivedCategory.Bounded.singleFunctor A 0) (obj_mem P)

namespace functor

/-- The underlying object of the lifted degree-zero embedding is the ordinary single object. -/
@[simp, stacks 0FCS "lifted degree-zero object computation"]
theorem obj_obj [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (X : P.FullSubcategory) :
    ((functor P).obj X).obj =
      (DerivedCategory.Bounded.singleFunctor A 0).obj X.obj := sorry

/-- The underlying map of the lifted degree-zero embedding is the ordinary single-object map. -/
@[simp, stacks 0FCS "lifted degree-zero map computation"]
theorem map_hom [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((functor P).map f).hom =
      (DerivedCategory.Bounded.singleFunctor A 0).map f.hom := sorry

end functor

end Single

namespace Homology

/-- Lifted degree-zero cohomology has bounded shift support on every object
of the bounded cohomology-in-`P` category. -/
@[stacks 0FCS]
theorem hasFiniteSupport [IsWeakSerreClass P]
    (X : DerivedCategory.Bounded.CohomologyIn P) :
    (functor P 0).shiftVanishingBounded X := sorry

end Homology

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn
