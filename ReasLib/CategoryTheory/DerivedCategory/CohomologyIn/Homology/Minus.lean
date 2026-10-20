module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Homological
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Above Cohomology Valued in the Coefficient Subcategory

This leaf lifts bounded-above derived cohomology from a cohomology-in object to
`P.FullSubcategory` and exposes its object and morphism computations and canonical shift sequence.
For a weak Serre `P`, every degree is homological by the generic full-subcategory lift instance.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.Minus.CohomologyIn.Homology

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A)

/-- Degree-`i` bounded-above cohomology, valued in `P.FullSubcategory`. -/
@[stacks 06UQ "bounded-above cohomology valued in the coefficient subcategory"]
abbrev functor (i : ℤ) :
    DerivedCategory.Minus.CohomologyIn P ⥤ P.FullSubcategory :=
  P.lift
    ((DerivedCategory.Minus.cohomologyIn P).ι ⋙
      DerivedCategory.Minus.homologyFunctor A i)
    (fun X ↦ X.property i)

/-- Forgetting lifted bounded-above cohomology recovers the ambient cohomology functor. -/
@[stacks 06UQ "underlying bounded-above cohomology comparison"]
noncomputable def compιIso (i : ℤ) :
    functor P i ⋙ P.ι ≅
      (DerivedCategory.Minus.cohomologyIn P).ι ⋙
        DerivedCategory.Minus.homologyFunctor A i :=
  P.liftCompιIso
    ((DerivedCategory.Minus.cohomologyIn P).ι ⋙
      DerivedCategory.Minus.homologyFunctor A i)
    (fun X ↦ X.property i)

namespace functor

/-- The underlying lifted bounded-above cohomology object is ordinary cohomology. -/
@[simp, stacks 06UQ "bounded-above lifted cohomology object computation"]
theorem obj_obj (i : ℤ) (X : DerivedCategory.Minus.CohomologyIn P) :
    ((functor P i).obj X).obj =
      (DerivedCategory.Minus.homologyFunctor A i).obj X.obj := sorry

/-- The underlying lifted bounded-above cohomology map is the ordinary cohomology map. -/
@[simp, stacks 06UQ "bounded-above lifted cohomology map computation"]
theorem map_hom (i : ℤ) {X Y : DerivedCategory.Minus.CohomologyIn P}
    (f : X ⟶ Y) :
    ((functor P i).map f).hom =
      (DerivedCategory.Minus.homologyFunctor A i).map f.hom := sorry

end functor

/-- The canonical shift sequence on lifted degree-zero bounded-above cohomology. -/
@[stacks 06UQ "shift sequence on lifted bounded-above cohomology"]
noncomputable instance shiftSequence [P.IsClosedUnderIsomorphisms] :
    (functor P 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

section

variable [IsWeakSerreClass P] (i : ℤ)

#synth (functor P i).IsHomological

end

end CategoryTheory.DerivedCategory.Minus.CohomologyIn.Homology
