/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.Homological
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology Valued in a Cohomology-In Subcategory

For an object of `DerivedCategory.CohomologyIn P`, degree-`i` cohomology canonically lands in
`P.FullSubcategory`.  This leaf packages that functor, its object and morphism computations, and
its canonical shift sequence.  When `P` is weak Serre, the generic abelian-full-subcategory lift
instance also makes every degree homological.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.CohomologyIn.Homology

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A)

/-- Degree-`i` cohomology of a cohomology-in object, valued in `P.FullSubcategory`. -/
@[stacks 06UQ "cohomology valued in the coefficient subcategory"]
abbrev functor (i : ℤ) :
    DerivedCategory.CohomologyIn P ⥤ P.FullSubcategory :=
  P.lift
    ((DerivedCategory.cohomologyIn P).ι ⋙
      DerivedCategory.homologyFunctor A i)
    (fun X ↦ X.property i)

/-- Forgetting the lifted cohomology functor recovers ordinary derived cohomology. -/
@[stacks 06UQ "underlying cohomology functor comparison"]
noncomputable def compιIso (i : ℤ) :
    functor P i ⋙ P.ι ≅
      (DerivedCategory.cohomologyIn P).ι ⋙
        DerivedCategory.homologyFunctor A i :=
  P.liftCompιIso
    ((DerivedCategory.cohomologyIn P).ι ⋙
      DerivedCategory.homologyFunctor A i)
    (fun X ↦ X.property i)

namespace functor

/-- The underlying object of lifted cohomology is the ordinary cohomology object. -/
@[simp, stacks 06UQ "lifted cohomology object computation"]
theorem obj_obj (i : ℤ) (X : DerivedCategory.CohomologyIn P) :
    ((functor P i).obj X).obj =
      (DerivedCategory.homologyFunctor A i).obj X.obj := sorry

/-- The underlying morphism of lifted cohomology is the ordinary cohomology map. -/
@[simp, stacks 06UQ "lifted cohomology map computation"]
theorem map_hom (i : ℤ) {X Y : DerivedCategory.CohomologyIn P}
    (f : X ⟶ Y) :
    ((functor P i).map f).hom =
      (DerivedCategory.homologyFunctor A i).map f.hom := sorry

end functor

/-- The canonical shift sequence on lifted degree-zero cohomology. -/
@[stacks 06UQ "shift sequence on lifted cohomology"]
noncomputable instance shiftSequence [P.IsClosedUnderIsomorphisms] :
    (functor P 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

section

variable [IsWeakSerreClass P] (i : ℤ)

#synth (functor P i).IsHomological

end

end CategoryTheory.DerivedCategory.CohomologyIn.Homology
