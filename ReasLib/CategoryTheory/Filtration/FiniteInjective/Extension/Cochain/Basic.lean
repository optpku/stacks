/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Cochain Functors of Finite Filtered Extensions

This file owns the bounded-below cochain functor induced by an additive filtered extension.
Associated-graded and forgetful comparisons live in separate leaves, so downstream users can
import only the structural view they need.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

namespace Extension

/-- The bounded-below cochain functor induced termwise by an additive filtered extension. -/
@[stacks 05U1 "bounded-below cochain functor of a filtered extension"]
def cochain {T : A ⥤+ B} (E : Extension T) :
    CochainComplex.Plus (category A) ⥤
      CochainComplex.Plus (FilteredObject.Finite.category B) :=
  E.functor.obj.mapCochainComplexPlus

namespace Cochain

/-- Objectwise computation for the bounded-below cochain functor of a filtered extension. -/
@[simp, stacks 05U1 "bounded-below cochain object computation"]
theorem obj_obj {T : A ⥤+ B} (E : Extension T)
    (K : CochainComplex.Plus (category A)) :
    (E.cochain.obj K).obj =
      (E.functor.obj.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded-below cochain functor of a filtered extension. -/
@[simp, stacks 05U1 "bounded-below cochain map computation"]
theorem map_hom {T : A ⥤+ B} (E : Extension T)
    {K L : CochainComplex.Plus (category A)} (f : K ⟶ L) :
    (E.cochain.map f).hom =
      (E.functor.obj.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom := sorry

end Cochain

end Extension

end CategoryTheory.FilteredObject.Finite.FilteredInjective
