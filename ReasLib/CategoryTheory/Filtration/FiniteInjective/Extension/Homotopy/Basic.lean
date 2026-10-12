/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Cochain.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy Functors of Finite Filtered Extensions

This file owns the bounded-below homotopy functor induced by an additive extension and its two
basic comparison isomorphisms.  Computation and naturality lemmas live in sibling leaves so a
downstream import can choose only the API it needs.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

namespace Extension

/-- The bounded-below homotopy functor induced by an additive filtered extension. -/
@[stacks 05U1]
def homotopy {T : A ⥤+ B} (E : Extension T) :
    HomotopyCategory.Plus (category A) ⥤
      HomotopyCategory.Plus (FilteredObject.Finite.category B) :=
  E.functor.obj.mapHomotopyCategoryPlus

namespace Homotopy

/-- Objectwise computation for the homotopy functor of a filtered extension. -/
@[simp, stacks 05U1 "bounded-below homotopy object computation"]
theorem obj_obj {T : A ⥤+ B} (E : Extension T)
    (K : HomotopyCategory.Plus (category A)) :
    (E.homotopy.obj K).obj =
      (E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the homotopy functor of a filtered extension. -/
@[simp, stacks 05U1 "bounded-below homotopy map computation"]
theorem map_hom {T : A ⥤+ B} (E : Extension T)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    (E.homotopy.map f).hom =
      (E.functor.obj.mapHomotopyCategory (ComplexShape.up ℤ)).map f.hom := sorry

/-- Mapping bounded-below complexes by an extension commutes with passage to the homotopy
category. -/
@[stacks 05U1 "bounded-below cochain-to-homotopy comparison"]
def quotientIso {T : A ⥤+ B} (E : Extension T) :
    E.cochain ⋙
        HomotopyCategory.Plus.quotient (FilteredObject.Finite.category B) ≅
      HomotopyCategory.Plus.quotient (category A) ⋙ E.homotopy :=
  Functor.Homotopy.Plus.quotientIso E.functor.obj

/-- The forgetful comparison of a filtered extension, transported to bounded-below homotopy
categories. -/
@[stacks 05U1 "bounded-below forgetful comparison"]
def forgetIso {T : A ⥤+ B} (E : Extension T) :
    E.homotopy ⋙
        (FilteredObject.Finite.Forget.functor B).mapHomotopyCategoryPlus ≅
      (forget A).mapHomotopyCategoryPlus ⋙
        T.obj.mapHomotopyCategoryPlus :=
  Functor.mapHomotopyCategoryPlusCompIso E.forgetIso ≪≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (forget A ⋙ T.obj))).symm

end Homotopy

end Extension

end CategoryTheory.FilteredObject.Finite.FilteredInjective
