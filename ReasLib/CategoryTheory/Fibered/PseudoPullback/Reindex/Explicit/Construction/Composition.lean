module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition Comparison for Explicit Fiber-Pullback Reindexing

This leaf owns the objectwise and natural composition comparisons for explicit-cleavage
reindexing of categorical pullbacks of fibers.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v uX uY uS vX vY vS

namespace CategoryTheory

namespace BasedCategory.PseudoPullback.reindex.explicit

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The objectwise comparison from direct reindexing of a fiber pullback along `g ≫ f` to
successive reindexing along `f` and `g`. -/
noncomputable def mapCompIsoApp
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS (g ≫ f)).obj P ≅
      (functor F G χX χY χS f ⋙
        functor F G χX χY χS g).obj P :=
  Pullback.Reindex.mapCompIsoApp
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) f g P

/-- The left component of the forward objectwise fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.hom.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (mapCompIsoApp F G χX χY χS f g P).hom.fst =
      (Functor.Cleavage.Reindex.compIsoApp χX f g P.fst).hom := sorry

/-- The right component of the forward objectwise fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.hom.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (mapCompIsoApp F G χX χY χS f g P).hom.snd =
      (Functor.Cleavage.Reindex.compIsoApp χY f g P.snd).hom := sorry

/-- The left component of the inverse objectwise fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.inv.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (mapCompIsoApp F G χX χY χS f g P).inv.fst =
      (Functor.Cleavage.Reindex.compIsoApp χX f g P.fst).inv := sorry

/-- The right component of the inverse objectwise fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.inv.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (mapCompIsoApp F G χX χY χS f g P).inv.snd =
      (Functor.Cleavage.Reindex.compIsoApp χY f g P.snd).inv := sorry

/-- The objectwise fiber-pullback composition comparisons are natural. -/
theorem mapCompIsoApp.naturality.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    (functor F G χX χY χS (g ≫ f)).map φ ≫
        (mapCompIsoApp F G χX χY χS f g Q).hom =
      (mapCompIsoApp F G χX χY χS f g P).hom ≫
        (functor F G χX χY χS f ⋙
          functor F G χX χY χS g).map φ := sorry

/-- Inverse naturality of the objectwise fiber-pullback composition comparison. -/
theorem mapCompIsoApp.naturality.inv
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    (functor F G χX χY χS f ⋙
        functor F G χX χY χS g).map φ ≫
      (mapCompIsoApp F G χX χY χS f g Q).inv =
    (mapCompIsoApp F G χX χY χS f g P).inv ≫
      (functor F G χX χY χS (g ≫ f)).map φ := sorry

/-- Direct and successive reindexing of categorical pullbacks of fibers are naturally
isomorphic. -/
@[stacks 0040 "explicit-cleavage composition comparison for fiber-pullback reindexing"]
noncomputable def mapCompIso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    functor F G χX χY χS (g ≫ f) ≅
      functor F G χX χY χS f ⋙
        functor F G χX χY χS g :=
  Pullback.Reindex.mapCompIso
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) f g

/-- The first component of the forward natural composition comparison is the cleavage
composition comparison in the left fiber. -/
@[simp]
theorem mapCompIso.hom.app.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((mapCompIso F G χX χY χS f g).hom.app P).fst =
      (Functor.Cleavage.Reindex.compIsoApp χX f g P.fst).hom := sorry

/-- The second component of the forward natural composition comparison is the cleavage
composition comparison in the right fiber. -/
@[simp]
theorem mapCompIso.hom.app.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((mapCompIso F G χX χY χS f g).hom.app P).snd =
      (Functor.Cleavage.Reindex.compIsoApp χY f g P.snd).hom := sorry

/-- The first component of the inverse natural composition comparison is the inverse cleavage
composition comparison in the left fiber. -/
@[simp]
theorem mapCompIso.inv.app.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((mapCompIso F G χX χY χS f g).inv.app P).fst =
      (Functor.Cleavage.Reindex.compIsoApp χX f g P.fst).inv := sorry

/-- The second component of the inverse natural composition comparison is the inverse cleavage
composition comparison in the right fiber. -/
@[simp]
theorem mapCompIso.inv.app.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((mapCompIso F G χX χY χS f g).inv.app P).snd =
      (Functor.Cleavage.Reindex.compIsoApp χY f g P.snd).inv := sorry

end BasedCategory.PseudoPullback.reindex.explicit

end CategoryTheory
