/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Cochain.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated Graded Comparison for Cochain Extensions

This leaf transports an extension's associated-graded comparison to bounded-below cochain
complexes. It exposes component and naturality equations without requiring applications to unfold
the two composition comparisons.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Cochain

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- The associated-graded comparison of a filtered extension, transported to bounded-below
cochain complexes. -/
@[stacks 05U1 "bounded-below cochain associated-graded comparison"]
noncomputable def gradedIso {T : A ⥤+ B} (E : Extension T) (p : ℤ) :
    E.cochain ⋙
        (FilteredObject.Finite.AssociatedGraded.functor B ⋙
          GradedObject.eval p).mapCochainComplexPlus ≅
      (FilteredInjective.GradedPiece.functor (A := A) p).mapCochainComplexPlus ⋙
        T.obj.mapCochainComplexPlus :=
  Functor.Cochain.Plus.compIso (E.gradedIso p) ≪≫
    (Functor.Cochain.Plus.compIso
      (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).symm

/-- The forward component of the bounded-below cochain associated-graded comparison. -/
@[simp, stacks 05U1 "bounded-below cochain associated-graded comparison computation"]
theorem gradedIso_hom_app {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    (K : CochainComplex.Plus (category A)) :
    (gradedIso E p).hom.app K =
      (Functor.Cochain.Plus.compIso (E.gradedIso p)).hom.app K ≫
        (Functor.Cochain.Plus.compIso
          (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).inv.app K := sorry

/-- The inverse component of the bounded-below cochain associated-graded comparison. -/
@[simp, stacks 05U1 "bounded-below cochain associated-graded comparison computation"]
theorem gradedIso_inv_app {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    (K : CochainComplex.Plus (category A)) :
    (gradedIso E p).inv.app K =
      (Functor.Cochain.Plus.compIso
          (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).hom.app K ≫
        (Functor.Cochain.Plus.compIso (E.gradedIso p)).inv.app K := sorry

/-- Forward naturality of the bounded-below cochain associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05U1
  "bounded-below cochain associated-graded comparison naturality"]
theorem gradedIso_hom_naturality {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    (E.cochain ⋙
          (FilteredObject.Finite.AssociatedGraded.functor B ⋙
            GradedObject.eval p).mapCochainComplexPlus).map f ≫
        (gradedIso E p).hom.app L =
      (gradedIso E p).hom.app K ≫
        ((FilteredInjective.GradedPiece.functor (A := A) p).mapCochainComplexPlus ⋙
          T.obj.mapCochainComplexPlus).map f := sorry

/-- Inverse naturality of the bounded-below cochain associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05U1
  "bounded-below cochain associated-graded comparison naturality"]
theorem gradedIso_inv_naturality {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    ((FilteredInjective.GradedPiece.functor (A := A) p).mapCochainComplexPlus ⋙
          T.obj.mapCochainComplexPlus).map f ≫
        (gradedIso E p).inv.app L =
      (gradedIso E p).inv.app K ≫
        (E.cochain ⋙
          (FilteredObject.Finite.AssociatedGraded.functor B ⋙
            GradedObject.eval p).mapCochainComplexPlus).map f := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Cochain
