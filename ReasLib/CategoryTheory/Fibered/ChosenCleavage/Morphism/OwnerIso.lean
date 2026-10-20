/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence

/-!
# Transport of selected reindexing comparisons along owner isomorphisms

The declarations in this module are the `2`-cell-level transport API for
selected reindexing comparisons.  They are independent of the construction of
the induced strong transformation.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}
variable {F G : X ⟶ Y}

/-- The reindexing comparisons of two owner morphisms form a natural square with the fiber
components of an owner isomorphism. This is the `2`-cell compatibility needed to transport
reindexing constructions without returning to total-category cartesian uniqueness. -/
theorem Reindex.mapIso.owner.hom.naturality (e : F ≅ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Functor.Chosen.reindex Y.p f).map ((fiberFunctorIso e U).hom.app x) ≫
        (Reindex.mapIso G f x).hom =
      (Reindex.mapIso F f x).hom ≫
        (fiberFunctorIso e V).hom.app
          ((Functor.Chosen.reindex X.p f).obj x) := sorry

/-- Conjugation form of compatibility between an owner isomorphism and the forward reindexing
comparison. This orientation directly rewrites the comparison belonging to the target owner
morphism. -/
theorem Reindex.mapIso.owner.hom.eq (e : F ≅ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso G f x).hom =
      (Functor.Chosen.reindex Y.p f).map ((fiberFunctorIso e U).inv.app x) ≫
        (Reindex.mapIso F f x).hom ≫
        (fiberFunctorIso e V).hom.app
          ((Functor.Chosen.reindex X.p f).obj x) := sorry

/-- Total-category readout of `Reindex.mapIso.owner.hom.eq`. It is provided explicitly
because cartesian-lift calculations frequently compare the underlying arrows. -/
theorem Reindex.mapIso.owner.hom.toTotal (e : F ≅ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso G f x).hom.1 =
      ((Functor.Chosen.reindex Y.p f).map
          ((fiberFunctorIso e U).inv.app x)).1 ≫
        (Reindex.mapIso F f x).hom.1 ≫
        ((fiberFunctorIso e V).hom.app
          ((Functor.Chosen.reindex X.p f).obj x)).1 := sorry

/-- Conjugation form of compatibility between an owner isomorphism and the inverse reindexing
comparison. -/
theorem Reindex.mapIso.owner.inv.eq (e : F ≅ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso G f x).inv =
      (fiberFunctorIso e V).inv.app
          ((Functor.Chosen.reindex X.p f).obj x) ≫
        (Reindex.mapIso F f x).inv ≫
        (Functor.Chosen.reindex Y.p f).map
          ((fiberFunctorIso e U).hom.app x) := sorry

/-- Total-category readout of `Reindex.mapIso.owner.inv.eq`. -/
theorem Reindex.mapIso.owner.inv.toTotal (e : F ≅ G)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso G f x).inv.1 =
      ((fiberFunctorIso e V).inv.app
          ((Functor.Chosen.reindex X.p f).obj x)).1 ≫
        (Reindex.mapIso F f x).inv.1 ≫
        ((Functor.Chosen.reindex Y.p f).map
          ((fiberFunctorIso e U).hom.app x)).1 := sorry


end FiberedCategoryOver

end CategoryTheory
