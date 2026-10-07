module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Family.CoverLifting
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.PresheafFiber

/-!
# Separation by directed refinements

This file owns separation of raw presheaf-fiber sections and the directed
refinement existence statements that preserve separation while adding
finite-cover lifts.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r q w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι] {S : ιᵒᵖ ⥤ C}

/-- `R.Separates F s s'` means that the presheaf-fiber map induced by `R` distinguishes the
two source sections. -/
def Separates [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) (F : Cᵒᵖ ⥤ Type q)
    (s s' : R.sourcePresheafFiber.obj F) : Prop :=
  R.presheafFiberMap.app F s ≠ R.presheafFiberMap.app F s'

namespace Separates

/-- The identity directed refinement separates two raw presheaf-fiber sections
exactly when they are distinct. -/
@[simp]
theorem id_iff [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) (F : Cᵒᵖ ⥤ Type q)
    (s s' : T.presheafFiber.obj F) :
    (DirectedRefinement.id T).Separates F s s' ↔ s ≠ s' := sorry

/-- Separation by a composite directed refinement is separation by the second
factor after applying the first presheaf-fiber map. -/
@[simp]
theorem comp_iff [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, w', q} R.target.diagram)
    (F : Cᵒᵖ ⥤ Type q) (s s' : R.sourcePresheafFiber.obj F) :
    (R.comp Q).Separates F s s' ↔
      Q.Separates F (R.presheafFiberMap.app F s)
        (R.presheafFiberMap.app F s') := sorry

/-- Lemma 7.39.1 (00YO): unequal raw sheaf-fiber sections can remain separate after a directed
refinement whose fiber map lifts a prescribed element through a finite covering family. -/
@[stacks 00YO]
theorem existsCoverLift
    {J : GrothendieckTopology C} [HasPullbacks C] [IsDirected ι (fun a b => a ≤ b)]
    (S : ιᵒᵖ ⥤ C) {F : Sheaf J (Type (max u v w))}
    {s s' : (EssentiallySmallFiber.presheafFiberMax S).obj
      ((sheafToPresheaf J (Type (max u v w))).obj F)}
    (h_ne : s ≠ s') {W : C} (cover : SemiRepresentableFamily.Over.{w'} W)
    [Finite cover.index] (h_cover : cover.toSieve ∈ J W)
    (f : (EssentiallySmallFiber.fiberMax S).obj W) :
    ∃ R : DirectedRefinement.{u, v, w, w, max u v w} S,
      R.Separates ((sheafToPresheaf J (Type (max u v w))).obj F) s s' ∧
        NatTrans.CoverLift.{u, v, max u v w, w'} R.fiberMap cover f := sorry

/-- Lemma 7.39.2 (00YP): unequal raw sheaf-fiber sections remain separate after a directed
refinement whose fiber map has lifts through every finite covering family. -/
@[stacks 00YP]
theorem existsFiniteCoverLifts
    {J : GrothendieckTopology C} [HasPullbacks C] [IsDirected ι (fun a b => a ≤ b)]
    (S : ιᵒᵖ ⥤ C) {F : Sheaf J (Type (max u v w))}
    {s s' : (EssentiallySmallFiber.presheafFiberMax S).obj
      ((sheafToPresheaf J (Type (max u v w))).obj F)}
    (h_ne : s ≠ s') :
    ∃ R : DirectedRefinement.{u, v, w, max u v w, max u v w} S,
      R.Separates ((sheafToPresheaf J (Type (max u v w))).obj F) s s' ∧
        NatTrans.FiniteCoverLifts.{u, v, max u v w, w} R.fiberMap J := sorry

namespace Target

/-- A strengthened separating refinement has finite-cover lifts for every target-fiber element,
not only for elements in the image of the source fiber. -/
theorem existsFiniteCoverLifts
    {J : GrothendieckTopology C} [HasPullbacks C] [IsDirected ι (fun a b => a ≤ b)]
    (S : ιᵒᵖ ⥤ C) {F : Sheaf J (Type (max u v w))}
    {s s' : (EssentiallySmallFiber.presheafFiberMax S).obj
      ((sheafToPresheaf J (Type (max u v w))).obj F)}
    (h_ne : s ≠ s') :
    ∃ R : DirectedRefinement.{u, v, w, max u v w, max u v w} S,
      R.Separates ((sheafToPresheaf J (Type (max u v w))).obj F) s s' ∧
        Functor.FiniteCoverLifts.{u, v, max u v w, w} R.target.fiber J := sorry

end Target

end Separates

end DirectedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
