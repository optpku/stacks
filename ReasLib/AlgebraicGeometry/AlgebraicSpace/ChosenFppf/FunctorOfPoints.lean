/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full

/-!
# Chosen fppf algebraic spaces and functors of points

The full chosen presentation `ChosenBigFppfSite.full` has all schemes as
carrier, so its slice over `S` is `Over S` and its slice topology is the
ordinary big fppf topology (`ChosenBigFppfSite.full_bigTopology`). Its sheaves
take values in `Type (u + 1)`, so an fppf sheaf of `Type u`-valued functors of
points is compared with it by `ULift`.

Under this comparison the chosen-site notion
`ChosenBigFppfSite.IsAlgebraicSpace` corresponds to the canonical class
`AlgebraicSpace.IsAlgebraicSpace` of Stacks, Definition 025Y.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Universe lifting of fppf sheaves of sets on `Over S` to sheaves on the
slice over `S` of the full chosen fppf presentation; the underlying presheaf of
the image of `F` is `F ⋙ uliftFunctor`. -/
def fullUliftSheafFunctor (S : Scheme.{u}) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (full.bigTopology S) (Type (u + 1)) :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1})
    (fun F ↦ by
      rw [full_bigTopology]
      exact (isSheaf_iff_isSheaf_of_type _ _).2
        (Presieve.isSheaf_comp_uliftFunctor _
          ((isSheaf_iff_isSheaf_of_type _ _).1 F.property)))

/-- The underlying presheaf of the universe lift of a sheaf is its composite
with `uliftFunctor`. -/
@[simp]
theorem fullUliftSheafFunctor_obj_obj (S : Scheme.{u})
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) :
    ((fullUliftSheafFunctor S).obj F).obj = F.obj ⋙ uliftFunctor.{u + 1} := rfl

/-- An fppf sheaf on `Over S` is an algebraic space over `S` in the canonical
functor-of-points sense if and only if its universe lift is an algebraic space
on the slice over `S` of the full chosen fppf presentation. -/
theorem isAlgebraicSpace_fullUliftSheafFunctor_obj_iff (S : Scheme.{u})
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) :
    IsAlgebraicSpace ((fullUliftSheafFunctor S).obj F) ↔
      AlgebraicSpace.IsAlgebraicSpace F.obj := sorry

end AlgebraicGeometry.ChosenBigFppfSite
