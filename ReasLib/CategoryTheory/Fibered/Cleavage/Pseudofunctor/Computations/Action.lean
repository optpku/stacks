module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

@[expose] public section

/-!
# Action of the pseudofunctor associated to a cleavage

This file exposes the object, functor, and morphism action and the bridge back to the intrinsic
factorization characterization of chosen reindexing.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The object action of the fiber pseudofunctor associated to a cleavage is the standard fiber
over the underlying base object. -/
@[simp]
theorem toPseudofunctor.obj (U : C) :
    χ.toPseudofunctor.obj (LocallyDiscrete.mk (Opposite.op U)) =
      Cat.of (Fiber p U) := sorry

/-- The functor action of the fiber pseudofunctor associated to a cleavage is its reindexing
functor. This is the construction-level equality complementary to
`toPseudofunctor.mapIso`. -/
@[simp]
theorem toPseudofunctor.map.toFunctor {U V : C} (f : V ⟶ U) :
    (χ.toPseudofunctor.map f.op.toLoc).toFunctor = χ.reindex f := sorry

/-- Objectwise computation of the action of the fiber pseudofunctor associated to a
cleavage. -/
@[simp]
theorem toPseudofunctor.map.obj
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (χ.toPseudofunctor.map f.op.toLoc).toFunctor.obj x =
      (χ.reindex f).obj x := sorry

/-- Morphismwise computation of the action of the fiber pseudofunctor associated to a
cleavage. -/
@[simp]
theorem toPseudofunctor.map.hom
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    (χ.toPseudofunctor.map f.op.toLoc).toFunctor.map φ =
      (χ.reindex f).map φ := sorry

/-- The map of `χ.toPseudofunctor` along `f.op` is canonically the reindexing functor
`f⁎[χ]`. -/
noncomputable def toPseudofunctor.mapIso {U V : C} (f : V ⟶ U) :
    (χ.toPseudofunctor.map f.op.toLoc).toFunctor ≅ f⁎[χ] :=
  eqToIso (congrArg (fun k ↦ k.toFunctor)
    (LocallyDiscrete.mkPseudofunctor_map
      (fun U ↦ Cat.of (Fiber p (unop U)))
      (fun f ↦ ((f.unop)⁎[χ]).toCatHom)
      (fun U ↦ Cat.Hom.isoMk ((Reindex.idIso χ (unop U)).symm))
      (fun f g ↦ Cat.Hom.isoMk (Reindex.compIso χ f.unop g.unop))
      (fun f g h ↦ toPseudofunctor.map₂.associator χ f g h)
      (fun f ↦ toPseudofunctor.map₂.leftUnitor χ f)
      (fun f ↦ toPseudofunctor.map₂.rightUnitor χ f)
      f.op.toLoc))

/-- The forward component of the map comparison is the pointwise transport supplied by the
object-action computation theorem. This keeps downstream code independent of the implementation
of `LocallyDiscrete.mkPseudofunctor`. -/
@[simp]
theorem toPseudofunctor.mapIso.hom.app
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (toPseudofunctor.mapIso χ f).hom.app x =
      eqToHom (toPseudofunctor.map.obj χ f x) := sorry

/-- The inverse component of the map comparison is the reverse pointwise transport supplied by
the object-action computation theorem. -/
@[simp]
theorem toPseudofunctor.mapIso.inv.app
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (toPseudofunctor.mapIso χ f).inv.app x =
      eqToHom (toPseudofunctor.map.obj χ f x).symm := sorry

/-- Reindexing by the pseudofunctor associated to a cleavage is characterized by factorization
through that cleavage's chosen strongly cartesian arrow. This is the representation bridge from
the bicategorical owner back to the intrinsic cleavage data. -/
@[reassoc]
theorem toPseudofunctor.map.fac
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    ((χ.toPseudofunctor.map f.op.toLoc).toFunctor.map φ).1 ≫ χ.cartesianHom f y =
      χ.cartesianHom f x ≫ φ.1 := sorry
/- Proof strategy: transport through `toPseudofunctor.mapIso`, then apply `reindexMap.fac`.
The statement is kept at the pseudofunctor boundary so downstream code never needs to unfold
`LocallyDiscrete.mkPseudofunctor`. -/

end Functor.Cleavage

end CategoryTheory
