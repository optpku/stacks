/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit Reindexing of Categorical Pullbacks of Fibers

This leaf specializes pointwise categorical-pullback reindexing to supplied cleavages and exposes
its projection and componentwise computation API.
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

/-- Reindex both legs of a categorical pullback of fibers and conjugate its structural
isomorphism by the cartesian-functor comparison isomorphisms. This is the specialization of
`IndexedFunctor.Pullback.Reindex.functor` to the two indexed fiber functors. -/
@[stacks 0040 "explicit-cleavage reindexing of categorical pullbacks of fibers"]
noncomputable def functor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) ⥤
      ((F.fiberFunctor V) ⊡ (G.fiberFunctor V)) :=
  Pullback.Reindex.functor
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) f

/-- The first projection of `functor` is reindexing in the left fiber. -/
noncomputable def fst.iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    functor F G χX χY χS f ⋙
        π₁ (F.fiberFunctor V) (G.fiberFunctor V) ≅
      π₁ (F.fiberFunctor U) (G.fiberFunctor U) ⋙ χX.reindex f :=
  Pullback.Reindex.fstIso
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) f

/-- The second projection of `functor` is reindexing in the right fiber. -/
noncomputable def snd.iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    functor F G χX χY χS f ⋙
        π₂ (F.fiberFunctor V) (G.fiberFunctor V) ≅
      π₂ (F.fiberFunctor U) (G.fiberFunctor U) ⋙ χY.reindex f :=
  Pullback.Reindex.sndIso
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS) f

/-- The left object component of `functor` is cleavage reindexing. -/
@[simp]
theorem functor.obj.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS f |>.obj P).fst =
      (χX.reindex f).obj P.fst := sorry

/-- The right object component of `functor` is cleavage reindexing. -/
@[simp]
theorem functor.obj.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS f |>.obj P).snd =
      (χY.reindex f).obj P.snd := sorry

/-- The structural isomorphism of a reindexed pullback object is obtained by applying the
middle reindexing functor and conjugating by the two cartesian-functor comparisons. -/
@[simp]
theorem functor.obj.iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS f |>.obj P).iso =
      (CartesianBasedFunctor.Reindex.mapIso F χX χS f P.fst).symm ≪≫
        (χS.reindex f).mapIso P.iso ≪≫
        CartesianBasedFunctor.Reindex.mapIso G χY χS f P.snd := sorry

/-- Forward-map computation for the structural isomorphism of cleavage-explicit
fiber-pullback reindexing. -/
@[simp]
theorem functor.obj.iso.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS f |>.obj P).iso.hom =
      (CartesianBasedFunctor.Reindex.mapIso F χX χS f P.fst).inv ≫
        (χS.reindex f).map P.iso.hom ≫
        (CartesianBasedFunctor.Reindex.mapIso G χY χS f P.snd).hom := sorry

/-- Inverse-map computation for the structural isomorphism of cleavage-explicit
fiber-pullback reindexing. -/
@[simp]
theorem functor.obj.iso.inv
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (functor F G χX χY χS f |>.obj P).iso.inv =
      (CartesianBasedFunctor.Reindex.mapIso G χY χS f P.snd).inv ≫
        (χS.reindex f).map P.iso.inv ≫
        (CartesianBasedFunctor.Reindex.mapIso F χX χS f P.fst).hom := sorry

/-- The left morphism component of `functor` is cleavage reindexing. -/
@[simp]
theorem functor.map.fst
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    (functor F G χX χY χS f |>.map φ).fst =
      (χX.reindex f).map φ.fst := sorry

/-- The right morphism component of `functor` is cleavage reindexing. -/
@[simp]
theorem functor.map.snd
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    (functor F G χX χY χS f |>.map φ).snd =
      (χY.reindex f).map φ.snd := sorry

end BasedCategory.PseudoPullback.reindex.explicit

end CategoryTheory
