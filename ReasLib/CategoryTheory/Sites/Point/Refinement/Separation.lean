/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.PresheafFiber

/-!
# Separation under ordered refinements

This leaf supplies computation rules for the neutral
`OrderedRefinement.EssentiallySmall.Separates` predicate.  It is independent of
saturation-stage packaging.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' r''

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.EssentiallySmall.Separates

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable (S : ιᵒᵖ ⥤ C)
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]

/-- The identity ordered refinement separates two fiber elements exactly when
the elements are distinct. -/
@[simp]
theorem id_iff (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P) :
    OrderedRefinement.EssentiallySmall.Separates (OrderedRefinement.id S) P x y ↔
      x ≠ y := sorry

/-- Distinct fiber elements are separated by the identity ordered refinement. -/
theorem id (P : Cᵒᵖ ⥤ Type q)
    {x y : (EssentiallySmallFiber.presheafFiber S).obj P} (hxy : x ≠ y) :
    OrderedRefinement.EssentiallySmall.Separates (OrderedRefinement.id S) P x y := sorry

section Composition

variable {ι' : Type r'} [Preorder ι']
variable {ι'' : Type r''} [Preorder ι'']
variable {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [EssentiallySmall.{q} ι'ᵒᵖ] [EssentiallySmall.{q} ι''ᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber U).Elementsᵒᵖ (Type q)]

/-- Separation by a composite ordered refinement is separation by the second
factor after applying the first presheaf-fiber map. -/
@[simp]
theorem comp_iff (R : OrderedRefinement S T) (Q : OrderedRefinement T U)
    (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P) :
    OrderedRefinement.EssentiallySmall.Separates (R.comp Q) P x y ↔
      OrderedRefinement.EssentiallySmall.Separates Q P
        ((OrderedRefinement.EssentiallySmall.presheafFiberMap R).app P x)
        ((OrderedRefinement.EssentiallySmall.presheafFiberMap R).app P y) := sorry

/-- Separation along an arbitrary factorization is computed by the two
factor maps, without requiring the total refinement to be definitionally a
composite. -/
theorem factorization_iff
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {Ptotal : OrderedRefinement S U}
    (h : OrderedRefinement.IsFactorization R Q Ptotal)
    (P : Cᵒᵖ ⥤ Type q)
    (x y : (EssentiallySmallFiber.presheafFiber S).obj P) :
    OrderedRefinement.EssentiallySmall.Separates Ptotal P x y ↔
      OrderedRefinement.EssentiallySmall.Separates Q P
        ((OrderedRefinement.EssentiallySmall.presheafFiberMap R).app P x)
        ((OrderedRefinement.EssentiallySmall.presheafFiberMap R).app P y) := sorry

end Composition

end OrderedRefinement.EssentiallySmall.Separates
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
