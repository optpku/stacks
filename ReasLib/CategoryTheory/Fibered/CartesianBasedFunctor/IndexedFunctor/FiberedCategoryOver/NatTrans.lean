module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Action

/-!
# Indexed modifications of fibred-category `2`-morphisms

For fixed fibred source and target, this module promotes the fiberwise action
on `2`-morphisms to indexed modifications and packages it as a functor on the
hom-category.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type uC} [Category.{vC} C]
variable {X : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable {Y : FiberedCategoryOver.{uC, vC, uS, vS} C}

/-- Fiber restrictions of a `2`-morphism are compatible with the indexed naturality
isomorphisms. -/
theorem Indexed.cell.naturality
    {F G : X ⟶ Y} (τ : F ⟶ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((Indexed.functor F).naturality f).hom.app x ≫
        ((Functor.fiberPseudofunctor Y.p).map
          f.op.toLoc).toFunctor.map ((fiberNatTrans τ U).app x) =
      (fiberNatTrans τ V).app
          (((Functor.fiberPseudofunctor X.p).map
            f.op.toLoc).toFunctor.obj x) ≫
        ((Indexed.functor G).naturality f).hom.app x := sorry

/-- Reindexing a component of an owner `2`-morphism is its component after reindexing,
conjugated by the comparison isomorphisms of the two boundary `1`-morphisms. -/
theorem Indexed.cell.reindex
    {F G : X ⟶ Y} (τ : F ⟶ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((Functor.fiberPseudofunctor Y.p).map
        f.op.toLoc).toFunctor.map ((fiberNatTrans τ U).app x) =
      (Reindex.mapIso F f x).hom ≫
        (fiberNatTrans τ V).app
          (((Functor.fiberPseudofunctor X.p).map
            f.op.toLoc).toFunctor.obj x) ≫
        (Reindex.mapIso G f x).inv := sorry

/-- Total-category readout of `fiberPseudofunctor_map_fiberNatTrans_app`. -/
theorem Indexed.cell.reindex.toTotal
    {F G : X ⟶ Y} (τ : F ⟶ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (((Functor.fiberPseudofunctor Y.p).map
        f.op.toLoc).toFunctor.map ((fiberNatTrans τ U).app x)).1 =
      (Reindex.mapIso F f x).hom.1 ≫
        ((fiberNatTrans τ V).app
          (((Functor.fiberPseudofunctor X.p).map
            f.op.toLoc).toFunctor.obj x)).1 ≫
        (Reindex.mapIso G f x).inv.1 := sorry

/-- A `2`-morphism of fibred-category morphisms induces a modification between their direct
indexed fiber actions. -/
def Indexed.cell
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    Indexed.functor F ⟶ Indexed.functor G where
  app U := fiberNatTrans τ U
  naturality f x := Indexed.cell.naturality τ f x

/-- Components of the direct indexed modification are the restricted fiber natural
transformations. -/
@[simp]
theorem Indexed.cell.app
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C) :
    (Indexed.cell τ).app U = fiberNatTrans τ U := sorry

/-- Objectwise components of the direct indexed modification are the fiber components of the
original `2`-morphism. -/
@[simp]
theorem Indexed.cell.app.component
    {F G : X ⟶ Y} (τ : F ⟶ G)
    (U : C) (x : X.p.Fiber U) :
    ((Indexed.cell τ).app U).app x =
      (fiberNatTrans τ U).app x := sorry

/-- Forgetting an objectwise component of the direct indexed modification recovers the
underlying total-category component. -/
@[simp]
theorem Indexed.cell.app.component.toTotal
    {F G : X ⟶ Y} (τ : F ⟶ G)
    (U : C) (x : X.p.Fiber U) :
    (((Indexed.cell τ).app U).app x).1 =
      τ.hom.toNatTrans.app x.1 := sorry

/-- The direct indexed modification construction preserves identity `2`-morphisms. -/
@[simp]
theorem Indexed.cell.id
    (F : X ⟶ Y) :
    Indexed.cell (𝟙 F) =
      𝟙 (Indexed.functor F) := sorry

/-- The direct indexed modification construction preserves vertical composition. -/
@[simp]
theorem Indexed.cell.comp
    {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    Indexed.cell (τ ≫ σ) =
      Indexed.cell τ ≫ Indexed.cell σ := sorry

/-- Two induced indexed cells are equal when all their fiber natural transformations agree. -/
theorem Indexed.cell.ext
    {F G : X ⟶ Y} {τ σ : F ⟶ G}
    (h : ∀ U : C, fiberNatTrans τ U = fiberNatTrans σ U) :
    Indexed.cell τ = Indexed.cell σ := sorry

variable (X Y) in
/-- For fixed fibred source and target, passage to the selected indexed fiber action is a
functor on the hom-category.

The endpoints are explicit because this owner has no value input from which Lean can recover the
fixed source and target fibred categories. -/
noncomputable def Indexed.homFunctor :
    (X ⟶ Y) ⥤
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
        (Functor.fiberPseudofunctor X.p)
        (Functor.fiberPseudofunctor Y.p) where
  obj F := Indexed.functor F
  map τ := Indexed.cell τ
  map_id F := Indexed.cell.id F
  map_comp τ σ := Indexed.cell.comp τ σ

/-- The object action of `Indexed.homFunctor` is `Indexed.functor`. -/
@[simp]
theorem Indexed.homFunctor.obj
    (F : X ⟶ Y) :
    (Indexed.homFunctor X Y).obj F =
      Indexed.functor F := sorry

/-- The morphism action of `Indexed.homFunctor` is `Indexed.cell`. -/
@[simp]
theorem Indexed.homFunctor.map
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    (Indexed.homFunctor X Y).map τ =
      Indexed.cell τ := sorry

/-- The component of the hom-functor map is the fiber restriction of the owner `2`-morphism. -/
@[simp]
theorem Indexed.homFunctor.map.app
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C) :
    ((Indexed.homFunctor X Y).map τ).app U = fiberNatTrans τ U := sorry

/-- The objectwise component of the hom-functor map is the fiber component of the owner
`2`-morphism. -/
@[simp]
theorem Indexed.homFunctor.map.app.component
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    (((Indexed.homFunctor X Y).map τ).app U).app x =
      (fiberNatTrans τ U).app x := sorry

/-- Forgetting an objectwise component of the hom-functor map recovers the original
total-category component. -/
@[simp]
theorem Indexed.homFunctor.map.app.component.toTotal
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    ((((Indexed.homFunctor X Y).map τ).app U).app x).1 =
      τ.hom.toNatTrans.app x.1 := sorry

/-- The hom-functor sends an identity owner `2`-morphism to the identity indexed
modification. -/
@[simp]
theorem Indexed.homFunctor.map.id (F : X ⟶ Y) :
    (Indexed.homFunctor X Y).map (𝟙 F) = 𝟙 (Indexed.functor F) := sorry

/-- The hom-functor sends vertical composition of owner `2`-morphisms to composition of
their indexed modifications. -/
@[simp]
theorem Indexed.homFunctor.map.comp
    {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    (Indexed.homFunctor X Y).map (τ ≫ σ) =
      (Indexed.homFunctor X Y).map τ ≫ (Indexed.homFunctor X Y).map σ := sorry

end FiberedCategoryOver

end CategoryTheory
