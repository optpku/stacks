/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.ChowGroup
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents

noncomputable section

universe w v u x

namespace ChowMotive

/-- A degreewise functor on a category extends canonically to its Karoubi envelope. -/
noncomputable def chowFunctor {k : Type u} [Field k]
    {GradedCorrespondence : Type u → Type v}
    [Category.{w} (GradedCorrespondence k)]
    (chow : ℤ → GradedCorrespondence k ⥤ ModuleCat.{x} ℚ) (i : ℤ) :
    ChowMotive k GradedCorrespondence ⥤ ModuleCat.{x} ℚ :=
  (functorExtension (GradedCorrespondence k) (ModuleCat.{x} ℚ)).obj (chow i)

/-- The extended degreewise functor at a projector is isomorphic to the image of
that projector. -/
theorem chowFunctor_obj_iso_chowGroup {k : Type u} [Field k]
    {GradedCorrespondence : Type u → Type v}
    [Category.{w} (GradedCorrespondence k)]
    (chow : ℤ → GradedCorrespondence k ⥤ ModuleCat.{x} ℚ)
    (M : ChowMotive k GradedCorrespondence) (i : ℤ) :
    Nonempty ((chowFunctor chow i).obj M ≅ chowGroup chow M i) := sorry

/-- The degree-`i` linear Hom functor on a Karoubi envelope is corepresented by
the object in Tate degree `-i`. -/
theorem chowRepresentedBy {k : Type u} [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℚ C]
    (tateObject : ℤ → C) :
    ∀ i : ℤ, Nonempty
      (((chowFunctor (k := k) (GradedCorrespondence := fun _ ↦ C)
          (fun j ↦ (linearCoyoneda ℚ C).obj (Opposite.op (tateObject (-j)))) i) ⋙
            forget (ModuleCat.{w} ℚ)).CorepresentableBy
        (tateObject (-i) : ChowMotive k (fun _ ↦ C))) := sorry

/-- The degree-`i` projector-image group is naturally equivalent to morphisms
from the object in Tate degree `-i`. -/
theorem chowGroup_equiv_hom {k : Type u} [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℚ C]
    (tateObject : ℤ → C) (M : ChowMotive k (fun _ ↦ C)) (i : ℤ) :
    Nonempty
      (chowGroup (k := k) (GradedCorrespondence := fun _ ↦ C)
          (fun j ↦ (linearCoyoneda ℚ C).obj (Opposite.op (tateObject (-j)))) M i ≃
        ((tateObject (-i) : ChowMotive k (fun _ ↦ C)) ⟶ M)) := sorry

end ChowMotive
