/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Modification
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-presheaf maps of morphisms of fibred categories

This file owns the map on canonical Hom-presheaves induced by a morphism of
fibred categories, together with its component, identity, and composition API.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.{u, v, uS, vS} C}

/-- A morphism of fibred categories induces the canonical map between the
Hom-presheaves of two objects in a fiber. -/
@[stacks 042V "fixed-universe Hom-presheaf map"]
noncomputable def presheafHomMap
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    (Functor.fiberPseudofunctor X.p).presheafHom x y ⟶
      (Functor.fiberPseudofunctor Y.p).presheafHom
        ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) :=
  (strongTrans F).presheafHomMap x y

/-- A component of the canonical Hom-presheaf map is the component induced by
the associated strong transformation. -/
@[simp, stacks 042V "component of fixed-universe Hom-presheaf map"]
theorem presheafHomMap.app
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (W : (Over U)ᵒᵖ) :
    (presheafHomMap F x y).app W =
      (strongTrans F).presheafHomMapApp x y W := sorry

/-- At the identity object of the slice, the canonical Hom-presheaf map is
the ordinary map on morphisms in the fiber. -/
@[stacks 042V "identity-fiber component of Hom-presheaf map"]
theorem presheafHomMap.app.identity
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (f : x ⟶ y) :
    (presheafHomMap F x y).app (op (Over.mk (𝟙 U)))
        ((Functor.fiberPseudofunctor X.p).presheafHomObjHomEquiv f) =
      (Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv
        ((fiberFunctor F U).map f) := sorry

/-- The identity morphism of a fibred category induces the identity map of
every canonical Hom-presheaf. -/
@[simp, stacks 042V "identity law for Hom-presheaf maps"]
theorem presheafHomMap.id
    {U : C} (x y : X.p.Fiber U) :
    presheafHomMap (𝟙 X) x y =
      𝟙 ((Functor.fiberPseudofunctor X.p).presheafHom x y) := sorry

/-- The canonical Hom-presheaf map preserves composition of morphisms of
fibred categories. -/
@[stacks 042V "composition law for Hom-presheaf maps"]
theorem presheafHomMap.comp
    (F : X ⟶ Y) (G : Y ⟶ Z) {U : C} (x y : X.p.Fiber U) :
    presheafHomMap (F ≫ G) x y =
      presheafHomMap F x y ≫
        presheafHomMap G ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y) := sorry

/- Axiom audit: the non-Prop data of `presheafHomMap` is inherited from the
canonical strong-transformation construction; deferred debt is confined to
its naturality and coherence laws. -/

end FiberedCategoryOver.Hom

end CategoryTheory
