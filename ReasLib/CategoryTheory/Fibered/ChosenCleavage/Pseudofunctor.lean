module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Computations

/-!
# Choice-specialized fiber pseudofunctors

The reusable construction of a fiber pseudofunctor is
`Functor.Cleavage.toPseudofunctor`, which keeps the cleavage explicit.  This module is the
separate application boundary for contexts where a projection is only known to be fibred and a
cleavage is selected with `Functor.Cleavage.ofIsFibered`.

Keeping this specialization in its own module makes the noncanonical choice visible in the import
graph while retaining a convenient API for applications that do not compare arbitrary cleavages.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

/-- The fiber pseudofunctor obtained from the selected mathlib cleavage of a fibred projection.

The choice-free owner is `Cleavage.toPseudofunctor`; this definition is its application-level
specialization along `Cleavage.ofIsFibered`. -/
@[stacks 02XN]
noncomputable def fiberPseudofunctor (p : S ⥤ C) [p.IsFibered] :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  (Cleavage.ofIsFibered p).toPseudofunctor

/-- The selected fiber pseudofunctor sends a base object to its standard fiber. -/
@[simp]
theorem FiberPseudofunctor.obj (p : S ⥤ C) [p.IsFibered] (U : C) :
    (fiberPseudofunctor p).obj (LocallyDiscrete.mk (Opposite.op U)) =
      Cat.of (p.Fiber U) := sorry

/-- The action of the selected fiber pseudofunctor on a base arrow is the selected reindexing
functor. -/
@[simp]
theorem FiberPseudofunctor.map.toFunctor (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) :
    ((fiberPseudofunctor p).map f.op.toLoc).toFunctor =
      Chosen.reindex p f := sorry

/-- Objectwise computation of selected fiber-pseudofunctor reindexing. -/
@[simp]
theorem FiberPseudofunctor.map.obj (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    ((fiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x =
      Chosen.reindexObj p f x := sorry

/-- Morphismwise computation of selected fiber-pseudofunctor reindexing. -/
@[simp]
theorem FiberPseudofunctor.map.hom (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((fiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ =
      Chosen.reindexMap p f φ := sorry

/-- The action of `fiberPseudofunctor p` along `f.op` is canonically the reindexing functor for the
selected cleavage. -/
noncomputable def FiberPseudofunctor.mapIso (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) :
    ((fiberPseudofunctor p).map f.op.toLoc).toFunctor ≅
      Chosen.reindex p f :=
  Cleavage.toPseudofunctor.mapIso (Cleavage.ofIsFibered p) f

/-- The forward component of the selected map comparison is the pointwise transport attached to
the selected object-action computation theorem. -/
@[simp]
theorem FiberPseudofunctor.mapIso.hom.app
    (p : S ⥤ C) [p.IsFibered] {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (FiberPseudofunctor.mapIso p f).hom.app x =
      eqToHom (FiberPseudofunctor.map.obj p f x) := sorry

/-- The inverse component of the selected map comparison is the reverse pointwise transport
attached to the selected object-action computation theorem. -/
@[simp]
theorem FiberPseudofunctor.mapIso.inv.app
    (p : S ⥤ C) [p.IsFibered] {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (FiberPseudofunctor.mapIso p f).inv.app x =
      eqToHom (FiberPseudofunctor.map.obj p f x).symm := sorry

/-- Reindexing through the selected fiber pseudofunctor is characterized by factorization through
the selected strongly cartesian arrow. -/
@[reassoc]
theorem FiberPseudofunctor.map.fac (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    (((fiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ).1 ≫
        Chosen.cartesianHom p f y =
      Chosen.cartesianHom p f x ≫ φ.1 := sorry

/-- The hom component of the identity comparison for the selected fiber pseudofunctor is the
inverse component of the selected cleavage unit comparison. -/
@[simp]
theorem FiberPseudofunctor.mapIdOp.hom.app (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapIdOp U).hom.toNatTrans.app x =
      (Chosen.Reindex.idIsoApp p U x).inv := sorry

/-- The inverse component of the identity comparison for the selected fiber pseudofunctor is the
forward component of the selected cleavage unit comparison. -/
@[simp]
theorem FiberPseudofunctor.mapIdOp.inv.app (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapIdOp U).inv.toNatTrans.app x =
      (Chosen.Reindex.idIsoApp p U x).hom := sorry

/-- The hom component of mathlib's standard identity comparison is the inverse selected unit
component. -/
@[simp]
theorem FiberPseudofunctor.mapId.hom.app (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapId
      (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app x =
        (Chosen.Reindex.idIsoApp p U x).inv := sorry

/-- The inverse component of mathlib's standard identity comparison is the forward selected unit
component. -/
@[simp]
theorem FiberPseudofunctor.mapId.inv.app (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapId
      (LocallyDiscrete.mk (Opposite.op U))).inv.toNatTrans.app x =
        (Chosen.Reindex.idIsoApp p U x).hom := sorry

/-- The hom component of the composition comparison for the selected fiber pseudofunctor is the
selected cleavage composition comparison. -/
@[simp]
theorem FiberPseudofunctor.mapCompOp.hom.app (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapCompOp f g).hom.toNatTrans.app x =
      (Chosen.Reindex.compIsoApp p f g x).hom := sorry

/-- The inverse component of the composition comparison for the selected fiber pseudofunctor is
the inverse selected cleavage comparison. -/
@[simp]
theorem FiberPseudofunctor.mapCompOp.inv.app (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapCompOp f g).inv.toNatTrans.app x =
      (Chosen.Reindex.compIsoApp p f g x).inv := sorry

/-- The hom component of mathlib's standard composition comparison is the selected cleavage
composition component. -/
@[simp]
theorem FiberPseudofunctor.mapComp.hom.app (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app x =
      (Chosen.Reindex.compIsoApp p f g x).hom := sorry

/-- The inverse component of mathlib's standard composition comparison is the inverse selected
cleavage composition component. -/
@[simp]
theorem FiberPseudofunctor.mapComp.inv.app (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    ((fiberPseudofunctor p).mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app x =
      (Chosen.Reindex.compIsoApp p f g x).inv := sorry

/-- Over a specified composite, the forward selected pseudofunctor component is the selected
specified-composite reindexing comparison. -/
@[simp]
theorem FiberPseudofunctor.mapCompOp'.hom.app
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    ((fiberPseudofunctor p).mapCompOp' f g gf hgf).hom.toNatTrans.app x =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom := sorry

/-- Over a specified composite, the inverse selected pseudofunctor component is the inverse
selected specified-composite reindexing comparison. -/
@[simp]
theorem FiberPseudofunctor.mapCompOp'.inv.app
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    ((fiberPseudofunctor p).mapCompOp' f g gf hgf).inv.toNatTrans.app x =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).inv := sorry

/-- The hom component of the composition comparison over a specified composite factors the
iterated selected cartesian arrows through the selected arrow over that composite. -/
@[reassoc]
theorem FiberPseudofunctor.mapCompOp'.hom.app.fac (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    (((fiberPseudofunctor p).mapCompOp' f g gf hgf).hom.toNatTrans.app x).1 ≫
        Chosen.cartesianHom p g (Chosen.reindexObj p f x) ≫
        Chosen.cartesianHom p f x =
      Chosen.cartesianHom p gf x := sorry

/-- The inverse component of the composition comparison over a specified composite factors the
selected cartesian arrow through the two iterated selected arrows. -/
@[reassoc]
theorem FiberPseudofunctor.mapCompOp'.inv.app.fac (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    (((fiberPseudofunctor p).mapCompOp' f g gf hgf).inv.toNatTrans.app x).1 ≫
        Chosen.cartesianHom p gf x =
      Chosen.cartesianHom p g (Chosen.reindexObj p f x) ≫
        Chosen.cartesianHom p f x := sorry

end Functor

end CategoryTheory
