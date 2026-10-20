/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Homological
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Cohomology Valued in the Coefficient Subcategory

This leaf lifts bounded derived cohomology from a cohomology-in object to
`P.FullSubcategory` and exposes its object and morphism computations and canonical shift sequence.
For a weak Serre `P`, every degree is homological by the generic full-subcategory lift instance.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn.Homology

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A)

/-- Degree-`i` bounded cohomology, valued in `P.FullSubcategory`. -/
@[stacks 06UQ "bounded cohomology valued in the coefficient subcategory"]
abbrev functor (i : ℤ) :
    DerivedCategory.Bounded.CohomologyIn P ⥤ P.FullSubcategory :=
  P.lift
    ((DerivedCategory.Bounded.cohomologyIn P).ι ⋙
      DerivedCategory.Bounded.homologyFunctor A i)
    (fun X ↦ X.property i)

/-- Forgetting lifted bounded cohomology recovers the ambient cohomology functor. -/
@[stacks 06UQ "underlying bounded cohomology comparison"]
noncomputable def compιIso (i : ℤ) :
    functor P i ⋙ P.ι ≅
      (DerivedCategory.Bounded.cohomologyIn P).ι ⋙
        DerivedCategory.Bounded.homologyFunctor A i :=
  P.liftCompιIso
    ((DerivedCategory.Bounded.cohomologyIn P).ι ⋙
      DerivedCategory.Bounded.homologyFunctor A i)
    (fun X ↦ X.property i)

namespace functor

/-- The underlying lifted bounded cohomology object is ordinary cohomology. -/
@[simp, stacks 06UQ "bounded lifted cohomology object computation"]
theorem obj_obj (i : ℤ) (X : DerivedCategory.Bounded.CohomologyIn P) :
    ((functor P i).obj X).obj =
      (DerivedCategory.Bounded.homologyFunctor A i).obj X.obj := sorry

/-- The underlying lifted bounded cohomology map is the ordinary cohomology map. -/
@[simp, stacks 06UQ "bounded lifted cohomology map computation"]
theorem map_hom (i : ℤ) {X Y : DerivedCategory.Bounded.CohomologyIn P}
    (f : X ⟶ Y) :
    ((functor P i).map f).hom =
      (DerivedCategory.Bounded.homologyFunctor A i).map f.hom := sorry

end functor

/-- The canonical shift sequence on lifted degree-zero bounded cohomology. -/
@[stacks 0FCS "shift sequence on lifted bounded cohomology"]
noncomputable instance shiftSequence [P.IsClosedUnderIsomorphisms] :
    (functor P 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

section

variable [IsWeakSerreClass P] (i : ℤ)

#synth (functor P i).IsHomological

end

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn.Homology
