/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Naturality isomorphisms for selected fiber actions

This module packages the objectwise selected-cleavage comparison into the
natural isomorphisms used by pseudofunctor and strong-transformation APIs.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The selected objectwise comparisons bundle into the natural isomorphism
`F_U ⋙ f⁎_Y ≅ f⁎_X ⋙ F_V`. -/
noncomputable def Reindex.natIso (F : X ⟶ Y) {U V : C} (f : V ⟶ U) :
    fiberFunctor F U ⋙ Functor.Chosen.reindex Y.p f ≅
      Functor.Chosen.reindex X.p f ⋙ fiberFunctor F V :=
  CartesianBasedFunctor.Reindex.natIso
    (toCartesianBasedFunctor F)
    X.chosenCleavage Y.chosenCleavage f

/-- The forward component of the bundled selected reindexing comparison is the objectwise
comparison `Reindex.mapIso`. -/
@[simp]
theorem Reindex.natIso.hom.app (F : X ⟶ Y) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    (Reindex.natIso F f).hom.app x = (Reindex.mapIso F f x).hom := sorry

/-- The inverse component of the bundled selected reindexing comparison is the inverse
objectwise comparison. -/
@[simp]
theorem Reindex.natIso.inv.app (F : X ⟶ Y) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    (Reindex.natIso F f).inv.app x = (Reindex.mapIso F f x).inv := sorry

/-- Pseudonaturality in the orientation required by a strong transformation of contravariant fiber
pseudofunctors. -/
noncomputable def Reindex.pseudonaturalityIso (F : X ⟶ Y) {U V : C} (f : V ⟶ U) :
    ((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor ⋙ fiberFunctor F V ≅
      fiberFunctor F U ⋙
        ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor :=
  (Reindex.natIso F f).symm

/-- The forward component of pseudonaturality is the inverse selected reindexing comparison. -/
@[simp]
theorem Reindex.pseudonaturalityIso.hom.app (F : X ⟶ Y) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    (Reindex.pseudonaturalityIso F f).hom.app x = (Reindex.mapIso F f x).inv := sorry

/-- The inverse component of pseudonaturality is the forward selected reindexing comparison. -/
@[simp]
theorem Reindex.pseudonaturalityIso.inv.app (F : X ⟶ Y) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    (Reindex.pseudonaturalityIso F f).inv.app x = (Reindex.mapIso F f x).hom := sorry

end FiberedCategoryOver

end CategoryTheory
