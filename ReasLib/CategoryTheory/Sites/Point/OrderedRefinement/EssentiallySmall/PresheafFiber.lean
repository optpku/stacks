module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Fiber
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.PresheafFiber

/-!
# Presheaf-fiber maps of essentially-small ordered refinements

This module attaches the raw presheaf-fiber reindexing map to an
`OrderedRefinement`.  The required element-category colimits remain explicit,
so this is the minimal layer usable without cofilteredness assumptions.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q w₀ w₁ w₂

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

namespace OrderedRefinement.EssentiallySmall

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]

/-- The raw presheaf-fiber map induced by a pure refinement of
essentially-small inverse systems. The element-category colimits are the
minimal assumptions needed by the construction. -/
noncomputable def presheafFiberMap (R : OrderedRefinement S T)
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)] :
    EssentiallySmallFiber.presheafFiber S ⟶ EssentiallySmallFiber.presheafFiber T :=
  Reindexing.EssentiallySmall.presheafFiber
    R.embedding.toOrderHom.toFunctor T R.restrictionIso

section Naturality

variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]

/-- The presheaf-fiber map of a pure ordered refinement commutes with the
canonical maps from stagewise sections. -/
@[simp, reassoc]
theorem toPresheafFiber_naturality
    (R : OrderedRefinement S T) (F : Cᵒᵖ ⥤ Type q)
    (X : C) (x : (EssentiallySmallFiber.fiber S).obj X) :
    EssentiallySmallFiber.toPresheafFiber S X x F ≫ (presheafFiberMap R).app F =
      EssentiallySmallFiber.toPresheafFiber T X ((fiberMap R).app X x) F := sorry

end Naturality

/-- `R.Separates P x y` means that the presheaf-fiber map of an ordered
refinement `R` distinguishes the two source fiber elements. -/
def Separates (R : OrderedRefinement S T)
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
    [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]
    (P : Cᵒᵖ ⥤ Type q) (x y : (EssentiallySmallFiber.presheafFiber S).obj P) : Prop :=
  (presheafFiberMap R).app P x ≠ (presheafFiberMap R).app P y

/-- The presheaf-fiber map of the identity pure refinement is the identity. -/
@[simp]
theorem presheafFiberMap_id (S : ιᵒᵖ ⥤ C)
    [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)] :
    presheafFiberMap (id S) = 𝟙 (EssentiallySmallFiber.presheafFiber S) := sorry

section Composition

variable [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber U).Elementsᵒᵖ (Type q)]

/-- The presheaf-fiber map of a composite pure refinement is the composite of
its presheaf-fiber maps. -/
@[simp]
theorem presheafFiberMap_comp
    (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    presheafFiberMap (R.comp Q) = presheafFiberMap R ≫ presheafFiberMap Q := sorry

end Composition

end OrderedRefinement.EssentiallySmall

namespace OrderedRefinement.IsFactorization.EssentiallySmall

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [CategoryTheory.EssentiallySmall.{q} ιᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι'ᵒᵖ]
  [CategoryTheory.EssentiallySmall.{q} ι''ᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber T).Elementsᵒᵖ (Type q)]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber U).Elementsᵒᵖ (Type q)]

/-- A factorization of pure refinements induces the corresponding composite
map on raw presheaf fibers. -/
theorem presheafFiberMap
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P) :
    OrderedRefinement.EssentiallySmall.presheafFiberMap P =
      OrderedRefinement.EssentiallySmall.presheafFiberMap R ≫
        OrderedRefinement.EssentiallySmall.presheafFiberMap Q := sorry

/-- The object component of the raw presheaf-fiber map induced by a
factorization. -/
theorem presheafFiberMap_app
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U}
    (h : IsFactorization R Q P) (F : Cᵒᵖ ⥤ Type q) :
    (OrderedRefinement.EssentiallySmall.presheafFiberMap P).app F =
      (OrderedRefinement.EssentiallySmall.presheafFiberMap R).app F ≫
        (OrderedRefinement.EssentiallySmall.presheafFiberMap Q).app F := sorry

end OrderedRefinement.IsFactorization.EssentiallySmall

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
