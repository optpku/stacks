/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.PresheafFiber

/-!
# Cofiltered presheaf-fiber maps of ordered refinements

For essentially-small inverse systems indexed by nonempty directed preorders,
this module supplies ordered-refinement maps on presheaf fibers without asking
downstream callers to provide element-category colimit instances.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v q w₀ w₁ w₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace OrderedRefinement.EssentiallySmall.Cofiltered

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]
variable [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable [Nonempty ι'] [IsDirected ι' (· ≤ ·)]

/-- The raw presheaf-fiber map of a pure refinement of essentially-small
cofiltered inverse systems. This convenience specialization derives the
element-category colimits from directedness and nonemptiness. -/
noncomputable abbrev presheafFiberMap (R : OrderedRefinement S T) :
    EssentiallySmallFiber.Cofiltered.presheafFiber S ⟶
      EssentiallySmallFiber.Cofiltered.presheafFiber T :=
  Reindexing.EssentiallySmall.Cofiltered.presheafFiber
    R.embedding.toOrderHom.toFunctor T R.restrictionIso

/-- The cofiltered presheaf-fiber map of a pure ordered refinement commutes
with canonical germ maps. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality
    (R : OrderedRefinement S T) (F : Cᵒᵖ ⥤ Type q)
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) :
    EssentiallySmallFiber.Cofiltered.toPresheafFiber S X x F ≫
        (presheafFiberMap R).app F =
      EssentiallySmallFiber.Cofiltered.toPresheafFiber T X
        ((OrderedRefinement.EssentiallySmall.fiberMap R).app X x) F := sorry

/-- The cofiltered presheaf-fiber map of the identity pure refinement is the
identity. -/
@[simp]
theorem presheafFiberMap.id (S : ιᵒᵖ ⥤ C) :
    presheafFiberMap (id S) =
      𝟙 (EssentiallySmallFiber.Cofiltered.presheafFiber S) := sorry

section Composition

variable [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]
variable [Nonempty ι''] [IsDirected ι'' (· ≤ ·)]

/-- The cofiltered presheaf-fiber map of a composite pure refinement is the
composite of its presheaf-fiber maps. -/
@[simp]
theorem presheafFiberMap.comp
    (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    presheafFiberMap (R.comp Q) =
      presheafFiberMap R ≫ presheafFiberMap Q := sorry

end Composition

end OrderedRefinement.EssentiallySmall.Cofiltered

namespace OrderedRefinement.IsFactorization.EssentiallySmall.Cofiltered

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]
variable [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable [Nonempty ι'] [IsDirected ι' (· ≤ ·)]
variable [Nonempty ι''] [IsDirected ι'' (· ≤ ·)]

/-- A factorization of pure refinements induces the corresponding composite
map on cofiltered presheaf fibers. -/
theorem presheafFiberMap
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P) :
    OrderedRefinement.EssentiallySmall.Cofiltered.presheafFiberMap P =
      OrderedRefinement.EssentiallySmall.Cofiltered.presheafFiberMap R ≫
        OrderedRefinement.EssentiallySmall.Cofiltered.presheafFiberMap Q := sorry

end OrderedRefinement.IsFactorization.EssentiallySmall.Cofiltered

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
